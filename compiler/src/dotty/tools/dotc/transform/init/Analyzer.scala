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

object Analyzer {
  def isPartial(tp: Type)(implicit ctx: Context) = tp.dealiasKeepAnnots.hasAnnotation(defn.PartialAnnot)
  def isFilled(tp: Type)(implicit ctx: Context) = tp.dealiasKeepAnnots.hasAnnotation(defn.FilledAnnot)

  def isPartial(sym: Symbol)(implicit ctx: Context) = sym.hasAnnotation(defn.PartialAnnot)
  def isFilled(sym: Symbol)(implicit ctx: Context) = sym.hasAnnotation(defn.FilledAnnot)
  def isInit(sym: Symbol)(implicit ctx: Context) = sym.hasAnnotation(defn.InitAnnot)

  def isPrimaryConstructorFields(sym: Symbol)(implicit ctx: Context) = sym.is(ParamAccessor)

  def typeState(tp: Type)(implicit ctx: Context) =
    if (isPartial(tp)) State.Partial
    else if (isFilled(tp)) State.Filled
    else State.Full

  def symbolState(sym: Symbol)(implicit ctx: Context) =
    if (isPartial(sym)) State.Partial
    else if (isFilled(sym)) State.Filled
    else State.Full

  def isConcreteField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Deferred | Method | Local | Private)

  def isNonParamField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Method | ParamAccessor | Lazy | Deferred)

  def isField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Method | Lazy | Deferred)
}

object Indexing {
  /** Index local definitions */
  def indexStats(stats: List[Tree], env: Env)(implicit ctx: Context): Unit = stats.foreach {
    case ddef: DefDef =>
      env.addTree(ddef.symbol, ddef)
    case vdef: ValDef if vdef.symbol.is(Lazy)  =>
      env.addTree(vdef.symbol,  vdef)
    case tdef: TypeDef if tdef.isClassDef  =>
      env.addTree(tdef.symbol, tdef.rhs)
    case _ =>
  }

  def indexTemplate(cls: ClassSymbol, tp: Type, tmpl: Template, env: Env, obj: ObjectRep): ObjectValue = {
    // index current class environment
    val innerEnv = env.fresh()
    indexStats(tmpl.body, innerEnv)
    obj.add(ClassEnv(innerEnv.id, tp))

    // index parent class environments
    val atom = new AtomObjectValue(obj.id)
    cls.baseClasses.tail.foldLeft(atom) { (parent, acc) =>
      val baseType = tp.baseType(parent)
      indexClass(parent, baseType, env, obj).join(acc)
    }
  }

  def indexClass(cls: ClassSymbol, tp: Type, env: Env, obj: ObjectRep)(implicit ctx: Context): ObjectValue = {
    def toPrefix(tp: Type): TypeRef = tp match {
      case AppliedType(tycon, _) => toPrefix(tycon.dealias)
      case tp: TypeRef => tp.prefix
    }

    def default = new AtomObjectValue(obj.id)

    val prefix = toPrefix(tp)
    if (prefix == NoPrefix) {
      // must exist in scope
      val (tmpl: Template, envId) = env.getTree(cls)
      val envOuter = env.heap(envId).asInstanceOf[Env]

      val innerEnv = envOuter.fresh()
      indexStats(tmpl.body, innerEnv)
      obj.add(ClassEnv(innerEnv.id, tp))
    }
    else {
      val prefixRes = checkRef(prefix, env, parent.pos)
      if (prefixRes.isLatent)
        prefixRes.latentValue.asObject.index(cls, tp, obj)
      else default
    }
  }

  def indexInnerClass(cls: ClassSymbol, tp: Type, inner: ObjectRep, outer: ObjectRep)(implicit ctx: Context): ObjectValue = {
    val enclosingCls = cls.owner
    if (outer.classEnv.contains(enclosingCls)) {
      val ClassEnv(envId, _) = outer.classEnv(enclosingCls)
      val env = outer.heap(envId)
      val (tmpl: Template, _) = env.getTree(cls)

      // don't go recursively for parents as indexing is based on linearization
      val innerEnv = env.fresh()
      indexStats(tmpl.body, innerEnv)
      inner.add(ClassEnv(innerEnv.id, tp))
    }

    new ObjectValue(inner.id)
  }

  def indexLocalClass(cls: ClassSymbol, tp: Type, inner: ObjectRep, env: Env)(implicit ctx: Context): ObjectValue = {
    if (env.contains(cls)) {
      val (tmpl: Template, _) = env.getTree(cls)

      // don't go recursively for parents as indexing is based on linearization
      val innerEnv = env.fresh()
      indexStats(tmpl.body, innerEnv)
      inner.add(ClassEnv(innerEnv.id, tp))
    }

    new ObjectValue(inner.id)
  }

  def initObject(cls: ClassSymbol, tmpl: Template, obj: ObjectRep)(implicit ctx: Context): Unit = {
    cls.typeRef.fields.foreach { field =>
      obj.add(field.symbol.name, SymInfo(assigned = false))
    }

    // primary constructor fields are init early
    tmpl.constr.vparamss.flatten.foreach { (param: ValDef) =>
      val sym = cls.info.member(param.name).suchThat(x => !x.is(Method)).symbol
      obj(sym) = SymInfo(assigned = true, value = Analyzer.typeState(sym.info))
    }
  }

  def indexOuter(cls: ClassSymbol, env: Env)(implicit ctx: Context) = {
    def recur(cls: Symbol, maxValue: OpaqueValue): Unit = if (cls.owner.exists) {
      val outerValue = symbolState(cls)
      val enclosingCls = cls.owner.enclosingClass

      if (!cls.owner.isClass || maxState == FullValue) {
        env.add(enclosingCls, SymInfo(value = FullValue))
        recur(enclosingCls, FullValue)
      }
      else {
        val meet = outerValue.join(maxValue)
        env.add(enclosingCls, SymInfo(value = meet)
        recur(enclosingCls, meet)
      }
    }
    recur(cls, PartialValue)
  }
}

class Analyzer {
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
    val paramInfos = fun.tpe.widen.paramInfoss.flatten

    // check params
    var effs = Vector.empty[Effect]

    if (funRes.isLatent) {
      val valInfos = args.map { arg =>
        val res = apply(arg, env)
        effs = effs ++ res.effects
        res.valueInfo
      }

      if (effs.size > 0) return Res(effects = effs)

      indentedDebug(s">>> calling $funSym")
      val res = funRes.latentValue.asMethod(valInfos, env.heap)
      if (res.hasErrors) res.effects = Vector(Latent(tree, res.effects))
      res
    }
    else {
      val valInfos = args.map { arg =>
        val res = apply(arg, env)
        effs = effs ++ res.effects

        if (res.isLatent)
          res.state = Rules.latentState(res.latentValue, env.heap, arg.pos)

        res.valueInfo
      }

      if (effs.size > 0) return Res(effects = effs)

      checkParams(funSym, valInfos, paramInfos, env, args.map(_.pos))
    }
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
      else {
        val symInfo = env(cls)
        Res(value = symInfo.value)
      }
    case tp @ SuperType(thistpe, supertpe) =>
      // TODO : handle `supertpe`
      checkRef(thistpe, env, pos)
  }

  def checkClosure(sym: Symbol, tree: Tree, env: Env)(implicit ctx: Context): Res =
    Res(latentValue = env(sym).latentValue)

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
        env.assign(tp.symbol, rhsRes.valueInfo, vdef.rhs.pos)
      case tp @ TermRef(prefix, _) =>
        val prefixRes = checkRef(prefix, env, vdef.rhs.pos)
        assert(!prefixRes.hasErrors)
        prefixRes.latentValue.asObject.assign(sym, rhsRes.valueInfo, env.heap, vdef.pos)
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
            env.assign(tp.symbol, rhsRes.valueInfo, rhs.pos)
          case tp @ TermRef(prefix, _) =>
            val prefixRes = checkRef(prefix, env, rhs.pos)
            prefixRes.value.assign(tp.symbol, rhsRes.valueInfo, env.heap, rhs.pos)
        }
      case sel @ Select(qual, _) =>
        val prefixRes = apply(qual, env)
        prefixRes.value.assign(sel.symbol, rhsRes.valueInfo, env.heap, rhs.pos)
    }
  }

  def checkParents(cls: ClassSymbol, parents: List[Tree], env: Env, obj: ObjectValue)(implicit ctx: Context): Res = {
    val baseClasses = cls.baseClasses.tail
    val parentsOrdered = baseClasses.map(p => parents.find(_.tpe.classSymbol `eq` p)).collect {
      case Some(parent) => parent
    }

    val covered = mutable.Set.empty[Symbo]

    parentsOrdered.foldLeft(Res()) { (acc, parent) =>
      parent match {
        case tree @ NewEx(tref, init, argss) =>
          // TODO: not all of them
          covered ++= tref.classSymbol.baseClasses
          val res = checkInit(tref, init, argss, env, obj)
          acc.copy(effects = acc.effects ++ res.effects)
        case _ =>

          Res()
      }
    }
  }

  def checkNew(tree: Tree, tref: TypeRef, init: TermRef, argss: List[List[Tree]], env: Env)implicit ctx: Context): Res = {
    val cls = tref.classSymbol
    val args = argss.flatten

    // setup constructor params
    var effs = Vector.empty[Effect]
    val values = args.map { arg =>
      val res = apply(arg, env)
      effs = effs ++ res.effects
      res.value
    }

    if (effs.nonEmpty) return Res(effs)

    val obj = env.newObject

    val scope: Scope =
      if (tref.prefix == NoPrefix) env
      else {
        val prefixRes = checkRef(tref.prefix, env, parent.pos)
        if (prefixRes.hasErrors) return prefixRes
        prefixRes.value
      }

    // index class environments
    val atom = scope.index(cls, tree.tp, obj)
    val value = cls.baseClasses.tail.foldLeft(atom) { (parent, acc) =>
      val baseType = tree.tpe.baseType(parent)
      indexClass(parent, baseType, env, obj).join(acc)
    }

    scope.init(cls, init.symbol, values, args.map(_.pos), env.heap, value, tree.pos)
  }

  def checkInit(tree: Tree, tref: TypeRef, init: TermRef, argss: List[List[Tree]], env: Env, obj: ObjectRep)implicit ctx: Context): Res = {
    val cls = tref.classSymbol
    val args = argss.flatten

    // setup constructor params
    var effs = Vector.empty[Effect]
    val values = args.map { arg =>
      val res = apply(arg, env)
      effs = effs ++ res.effects
      res.value
    }

    if (effs.nonEmpty) return Res(effs)

    // TODO: prefix can be NoPrefix
    val scope: Scope =
      if (tref.prefix == NoPrefix) env
      else {
        val prefixRes = checkRef(tref.prefix, env, parent.pos)
        if (prefixRes.hasErrors) return prefixRes
        prefixRes.value
      }

    scope.init(cls, init.symbol, values, args.map(_.pos), env.heap, obj, tree.pos)
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
    checkParents(tmpl.parents, env, obj).join(checkStats(tmpl.body, env))
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