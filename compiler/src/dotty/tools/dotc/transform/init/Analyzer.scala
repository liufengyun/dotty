package dotty.tools.dotc
package transform
package init

import core._
import MegaPhase._
import Contexts.Context
import StdNames._
import Names._
import Phases._
import ast._
import Trees._
import Flags._
import SymUtils._
import Symbols._
import Denotations._
import SymDenotations._
import Types._
import Decorators._
import DenotTransformers._
import util.Positions._
import config.Printers.init.{ println => debug }
import Constants.Constant
import collection.mutable


class Analyzer extends Indexer {
  import tpd._

  var depth: Int = 0
  val indentTab = " "

  def trace[T](msg: String, env: Env)(body: => T) = {
    indentedDebug(s"==> ${pad(msg)}?")
    indentedDebug(env.toString)
    depth += 1
    val res = body
    depth -= 1
    indentedDebug(s"<== ${pad(msg)} = ${pad(res.toString)}")
    res
  }

  def padding = indentTab * depth

  def pad(s: String, padFirst: Boolean = false) =
    s.split("\n").mkString(if (padFirst) padding else "", "\n" + padding, "")

  def indentedDebug(msg: String) = debug(pad(msg, padFirst = true))

  def checkApply(tree: tpd.Tree, fun: Tree, argss: List[List[Tree]], env: Env)(implicit ctx: Context): Res = {
    val funSym = fun.symbol
    val funRes = apply(fun, env)

    // reduce reported errors
    if (funRes.hasErrors) return Res(effects = funRes.effects)

    val args = argss.flatten

    // check params
    var effs = Vector.empty[Effect]

    val values = args.map { arg =>
      val res = apply(arg, env)
      effs = effs ++ res.effects
      res.value
    }

    if (effs.size > 0) return Res(effects = effs)

    indentedDebug(s">>> calling $funSym")
    val res = funRes.value(values, args.map(_.pos), tree.pos, env.heap)
    if (res.hasErrors) res.effects = Vector(Latent(tree, res.effects))
    res
  }

  def checkSelect(tree: Select, env: Env)(implicit ctx: Context): Res = {
    val prefixRes = apply(tree.qualifier, env)

    // reduce reported errors
    if (prefixRes.hasErrors) return Res(effects = prefixRes.effects)

    prefixRes.value.select(tree.symbol, env.heap, tree.pos)
  }

  private def enclosedIn(curSym: Symbol, inSym: Symbol)(implicit ctx: Context): Boolean =
    curSym.exists && ((curSym `eq` inSym) || (enclosedIn(curSym.owner, inSym)))

  def checkRef(tp: Type, env: Env, pos: Position)(implicit ctx: Context): Res = tp match {
    case tp : TermRef if tp.symbol.is(Module) && enclosedIn(ctx.owner, tp.symbol.moduleClass) =>
      // self reference by name: object O { ... O.xxx }
      checkRef(ThisType.raw(ctx.owner.typeRef), env, pos)
    case tp @ TermRef(NoPrefix, _) =>
      env.select(tp.symbol, pos)
    case tp @ TermRef(prefix, _) =>
      val res = checkRef(prefix, env, pos)
      res.value.select(tp.symbol, env.heap, pos)
    case tp @ ThisType(tref) =>
      val cls = tref.symbol
      if (cls.is(Package)) Res() // Dotty represents package path by ThisType
      else Res(value = env(cls))
    case tp @ SuperType(thistpe, supertpe) =>
      // TODO : handle `supertpe`
      checkRef(thistpe, env, pos)
  }

  def checkClosure(sym: Symbol, tree: Tree, env: Env)(implicit ctx: Context): Res = {
    if (env.contains(sym)) Res(value = env(sym)) else Res()
  }

  def checkIf(tree: If, env: Env)(implicit ctx: Context): Res = {
    val If(cond, thenp, elsep) = tree

    val condRes: Res = apply(cond, env)

    val envClone = env.deepClone
    val thenRes: Res = apply(thenp, env)
    val elseRes: Res = apply(elsep, envClone)

    env.heap.join(envClone.heap)

    thenRes ++= condRes.effects
    thenRes.join(elseRes)
  }

  def checkValDef(vdef: ValDef, env: Env)(implicit ctx: Context): Res = {
    val rhsRes = apply(vdef.rhs, env)
    val sym = vdef.symbol

    // take `_` as uninitialized, otherwise it's initialized
    if (!tpd.isWildcardArg(vdef.rhs)) sym.termRef match {
      case tp @ TermRef(NoPrefix, _) =>
        env.assign(tp.symbol, rhsRes.value, vdef.rhs.pos)
      case tp @ TermRef(prefix, _) =>
        val prefixRes = checkRef(prefix, env, vdef.rhs.pos)
        assert(!prefixRes.hasErrors)
        prefixRes.value.assign(sym, rhsRes.value, env.heap, vdef.pos)
    }

    Res(effects = rhsRes.effects)
  }

  def checkStats(stats: List[Tree], env: Env)(implicit ctx: Context): Res =
    stats.foldLeft(Res()) { (acc, stat) =>
      indentedDebug(s"acc = ${pad(acc.toString)}")
      val res1 = apply(stat, env)
      acc.copy(effects = acc.effects ++ res1.effects)
    }

  def checkBlock(tree: Block, env: Env)(implicit ctx: Context): Res = {
    val newEnv = env.fresh()
    indexStats(tree.stats, newEnv)

    val res1 = checkStats(tree.stats, newEnv)
    val res2 = apply(tree.expr, newEnv)

    res2.copy(effects = res1.effects ++ res2.effects)
  }

  protected var _methChecking: Set[Symbol] = Set()
  def isChecking(sym: Symbol)   = _methChecking.contains(sym)
  def checking[T](sym: Symbol)(fn: => T) = {
    _methChecking += sym
    val res = fn
    _methChecking -= sym
    res
  }

  def checkAssign(lhs: Tree, rhs: Tree, env: Env)(implicit ctx: Context): Res = {
    val rhsRes = apply(rhs, env)
    if (rhsRes.hasErrors) return rhsRes

    lhs match {
      case ident @ Ident(_) =>
        ident.tpe match {
          case tp @ TermRef(NoPrefix, _) =>
            env.assign(tp.symbol, rhsRes.value, rhs.pos)
          case tp @ TermRef(prefix, _) =>
            val prefixRes = checkRef(prefix, env, rhs.pos)
            if (prefixRes.hasErrors) prefixRes
            else prefixRes.value.assign(tp.symbol, rhsRes.value, env.heap, rhs.pos)
        }
      case sel @ Select(qual, _) =>
        val prefixRes = apply(qual, env)
        prefixRes.value.assign(sel.symbol, rhsRes.value, env.heap, rhs.pos)
    }
  }

  def checkParents(cls: ClassSymbol, parents: List[Tree], env: Env, obj: ObjectRep)(implicit ctx: Context): Res = {
    if (cls.is(Trait)) return Res()

    // first call super class, see spec 5.1 about "Template Evaluation".
    parents.head match {
      case parent @ NewEx(tref, init, argss) =>
        val res = checkParent(init.symbol, argss, env, obj, parent.pos)
        if (res.hasErrors) return res
    }

    val superCls = parents.head.tpe.classSymbol
    val remains = cls.baseClasses.tail.takeWhile(_ `ne` superCls).reverse

    var resReturn = Res()

    // handle remaning traits
    remains.foreach { traitCls =>
      val parentOpt = parents.find(_.tpe.classSymbol `eq` traitCls)
      parentOpt match {
        case Some(parent @ NewEx(tref, init, argss)) =>
          val res = checkParent(init.symbol, argss, env, obj, parent.pos)
          resReturn = resReturn.join(res)
        case _ =>
          val res = checkParent(traitCls.primaryConstructor, Nil, env, obj, cls.pos)
          resReturn = resReturn.join(res)
      }
    }

    resReturn
  }

  def checkNew(tree: Tree, tref: TypeRef, init: TermRef, argss: List[List[Tree]], env: Env)(implicit ctx: Context): Res = {
    val cls = tref.classSymbol.asClass
    val args = argss.flatten

    // setup constructor params
    var effs = Vector.empty[Effect]
    val argValues = args.map { arg =>
      val res = apply(arg, env)
      effs = effs ++ res.effects
      res.value
    }

    if (effs.nonEmpty) return Res(effs)

    val obj = env.newObject(tree.tpe, open = false)

    def toPrefix(tp: Type): Type = tp match {
      case AppliedType(tycon, _) => toPrefix(tycon.dealias)
      case tp: TypeRef => tp.prefix
    }

    // index class environments
    val objs = cls.baseClasses.flatMap { parent =>
      val baseType = tree.tpe.baseType(parent)
      val prefix = toPrefix(baseType)
        if (prefix == NoPrefix) env.index(cls, obj, this)
        else {
          val prefixRes = checkRef(prefix, env, parent.pos)
          if (prefixRes.hasErrors) return prefixRes
          prefixRes.value.index(cls, obj, this)
        }
    }

    val objValues = objs.map { obj =>
      val res = obj(init.symbol).apply(argValues, args.map(_.pos), tree.pos, obj.heap)
      obj.init = true
      // reduce number of errors
      if (res.hasErrors) return Res(effects = res.effects)

      // an opaque object is subject to type checking
      if (obj.isOpaque) res.value.asInstanceOf[OpaqueValue]
      else new ObjectValue(obj.id)
    }

    if (objValues.size == 1) Res(value = objValues.head)
    else Res(value = new UnionValue(objValues.toSet))
  }

  /** Check a parent call
   *
   *  The result is only checked for errors, the value is only meaningful for
   *  the top-level `init` called in `checkNew`.
   *
   *  Disregard the prefix, as it is already handled in `index`.
   */
  def checkParent(init: Symbol, argss: List[List[Tree]], env: Env, obj: ObjectRep, pos: Position)(implicit ctx: Context): Res = {
    val args = argss.flatten

    // setup constructor params
    var effs = Vector.empty[Effect]
    val argValues = args.map { arg =>
      val res = apply(arg, env)
      effs = effs ++ res.effects
      res.value
    }

    if (effs.nonEmpty) return Res(effs)

    obj(init).apply(argValues, args.map(_.pos), pos, obj.heap)
  }

  object NewEx {
    def extract(tp: Type)(implicit ctx: Context): TypeRef = tp.dealias match {
      case tref: TypeRef => tref
      case AppliedType(tref: TypeRef, targs) => tref
    }

    def unapply(tree: tpd.Tree)(implicit ctx: Context): Option[(TypeRef, TermRef, List[List[tpd.Tree]])] = {
      val (fn, targs, vargss) = tpd.decomposeCall(tree)
      if (!fn.symbol.isConstructor || !tree.isInstanceOf[tpd.Apply]) None
      else {
        val Select(New(tpt), _) = fn
        Some((extract(tpt.tpe),  fn.tpe.asInstanceOf[TermRef], vargss))
      }
    }
  }

  def checkTemplate(cls: ClassSymbol, tp: Type, tmpl: Template, env: Env, obj: ObjectRep)(implicit ctx: Context) = {
    checkParents(cls, tmpl.parents, env, obj).join(checkStats(tmpl.body, env))
  }

  def apply(tree: Tree, env: Env)(implicit ctx: Context): Res = trace("checking " + tree.show, env)(tree match {
    case vdef : ValDef if !vdef.symbol.is(Lazy) && !vdef.rhs.isEmpty =>
      checkValDef(vdef, env)
    case _: DefTree =>  // ignore, definitions, already indexed
      Res()
    case Closure(_, meth, _) =>
      checkClosure(meth.symbol, tree, env)
    case tree: Ident if tree.symbol.isTerm =>
      checkRef(tree.tpe, env, tree.pos)
    case tree: This =>
      checkRef(tree.tpe, env, tree.pos)
    case tree: Super =>
      checkRef(tree.tpe, env, tree.pos)
    case tree: Select if tree.symbol.isTerm =>
      checkSelect(tree, env)
    case tree: If =>
      checkIf(tree, env)
    case tree @ NewEx(tref, init, argss) => // must before Apply
      checkNew(tree, tref, init, argss, env)
    case tree: Apply =>
      val (fn, targs, vargss) = decomposeCall(tree)
      checkApply(tree, fn, vargss, env)
    case tree @ Assign(lhs, rhs) =>
      checkAssign(lhs, rhs, env)
    case tree: Block =>
      checkBlock(tree, env)
    case Typed(expr, _) =>
      apply(expr, env)
    case _ =>
      Res()
  })
}