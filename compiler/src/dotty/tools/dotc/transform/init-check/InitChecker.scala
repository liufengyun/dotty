package dotty.tools.dotc
package transform

import core._
import MegaPhase._
import Contexts.Context
import StdNames._
import Phases._
import ast._
import Trees._
import Flags._
import SymUtils._
import Symbols._
import SymDenotations._
import Types._
import Decorators._
import DenotTransformers._
import util.Positions._
import config.Printers.init.{ println => debug }
import Constants.Constant
import collection.mutable

object InitChecker {
  val name = "initChecker"
}

import DataFlowChecker._

/** This transform checks initialization is safe based on data-flow analysis
 *
 *  Partial values:
 *   - partial values cannot be used as full values
 *   - a partial value can only be assigned to uninitialized field of a partial value
 *   - selection on a partial value is an error, unless the accessed field is known to be fully initialized
 *
 *  Init methods:
 *   - methods called during initialization should be annotated with `@init` or non-overridable
 *   - an `@init` method should not call overridable non-init methods
 *   - an overriding or implementing `@init` may only access param fields or other init-methods on `this`
 *   - otherwise, it may access non-param fields on `this`
 *
 *  Partial values are defined as follows:
 *   - params with the type `T @partial`
 *   - `this` in constructor unless it's known to be fully initialized
 *   - `new C(args)`, if any argument is partial
 *   - `val x = rhs` where the right-hand-side is partial
 *
 *  TODO:
 *   - default arguments of partial/init methods
 *   - selection on ParamAccessors of partial value is fine if the param is not partial
 *   - handle tailrec calls during initialization (which captures `this`)
 *
 */
class InitChecker extends MiniPhase with IdentityDenotTransformer { thisPhase =>
  import tpd._

  override def phaseName: String = InitChecker.name

  override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context): tpd.Tree = {
    tree
  }

  override def transformTemplate(tree: Template)(implicit ctx: Context): Tree = {
    val cls = ctx.owner.asClass

    if (cls.hasAnnotation(defn.UncheckedAnnot)) return tree

    val accessors = cls.paramAccessors.filterNot(x => x.isSetter)

    var noninit = Set[Symbol]()    // definitions that are not initialized
    var partial = Set[Symbol]()    // definitions that are partial initialized

    def isPartial(sym: Symbol) = sym.info.hasAnnotation(defn.PartialAnnot)

    def isConcreteField(sym: Symbol) =
      sym.isTerm && sym.is(AnyFlags, butNot = Deferred | Method | Local | Private)

    def isNonParamField(sym: Symbol) =
      sym.isTerm && sym.is(AnyFlags, butNot = Method | ParamAccessor | Lazy | Deferred)

    // partial fields of current class
    for (
      param <- accessors
      if isPartial(param)
    )
    partial += param

    // partial fields of super class
    for (
      parent <- cls.baseClasses.tail;
      decl <- parent.info.decls.toList
      if isConcreteField(decl) && isPartial(decl)
    )
    partial += decl

    // add current this
    partial += cls

    // non-initialized fields of current class
    for (
      decl <- cls.info.decls.toList
      if isNonParamField(decl)
    )
    noninit += decl

    val env: Env = (new FreshEnv).setNonInit(noninit).setPartialSyms(partial).setCurrentClass(cls)
    val checker = new DataFlowChecker

    val res = checker(env, tree)
    res.effects.foreach(_.report)
    res.env.nonInit.foreach { sym =>
      ctx.warning(s"field ${sym.name} is not initialized", sym.pos)
    }

    tree
  }
}

object DataFlowChecker {
  sealed trait Effect {
    def report(implicit ctx: Context): Unit = this match {
      case Member(sym, obj, pos)    =>
        ctx.warning(s"Select $sym on partial value ${obj.show}", pos)
      case Uninit(sym, pos)         =>
        ctx.warning(s"Reference to uninitialized value `${sym.name}`", pos)
      case OverrideRisk(sym, pos)     =>
        ctx.warning(s"`@scala.annotation.init` is recommended for abstract $sym for safe initialization", sym.pos)
        ctx.warning(s"Reference to $sym which could be overriden", pos)
      case Call(sym, effects, pos)  =>
        ctx.warning(s"The call to `${sym.name}` causes initialization problem", pos)
        effects.foreach(_.report)
      case Force(sym, effects, pos) =>
        ctx.warning(s"Forcing lazy val `${sym.name}` causes initialization problem", pos)
        effects.foreach(_.report)
      case Argument(sym, arg)       =>
        ctx.warning(s"Use partial value ${arg.show} as a full value to ${sym.show}", arg.pos)
      case CrossAssign(lhs, rhs)    =>
        ctx.warning(s"Assign partial value to a non-partial value", rhs.pos)
      case PartialNew(prefix, cls, pos)  =>
        ctx.warning(s"Cannot create $cls because the prefix `${prefix.show}` is partial", pos)
      case Instantiate(cls, effs, pos)  =>
        ctx.warning(s"Create instance results in initialization errors", pos)
        effs.foreach(_.report)
      case UseAbstractDef(sym, pos)  =>
         ctx.warning(s"`@scala.annotation.init` is recommended for abstract $sym for safe initialization", sym.pos)
         ctx.warning(s"Reference to abstract $sym which should be annotated with `@scala.annotation.init`", pos)
      case Latent(tree, effs)  =>
        effs.foreach(_.report)
        ctx.warning(s"Latent effects results in initialization errors", tree.pos)
    }
  }
  case class Uninit(sym: Symbol, pos: Position) extends Effect                         // usage of uninitialized values
  case class OverrideRisk(sym: Symbol, pos: Position) extends Effect                   // calling methods that are not override-free
  case class Call(sym: Symbol, effects: Seq[Effect], pos: Position) extends Effect     // calling method results in error
  case class Force(sym: Symbol, effects: Seq[Effect], pos: Position) extends Effect    // force lazy val results in error
  case class Argument(fun: Symbol, arg: tpd.Tree) extends Effect                       // use of partial values as full values
  case class Member(sym: Symbol, obj: tpd.Tree, pos: Position) extends Effect          // select members of partial values
  case class CrossAssign(lhs: tpd.Tree, rhs: tpd.Tree) extends Effect                  // assign a partial values to non-partial value
  case class PartialNew(prefix: Type, cls: Symbol, pos: Position) extends Effect       // create new inner class instance while outer is partial
  case class Instantiate(cls: Symbol, effs: Seq[Effect], pos: Position) extends Effect // create new instance of in-scope inner class results in error
  case class UseAbstractDef(sym: Symbol, pos: Position) extends Effect                 // use abstract def during initialization, see override5.scala
  case class Latent(tree: tpd.Tree, effs: Seq[Effect]) extends Effect                  // problematic latent effects (e.g. effects of closures)

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

  type Effects = Vector[Effect]
  // type LatentInfo = (Env, Seq[(Boolean, LatentInfo)]) => Res
  case class LatentInfo(fun: (Env, Int => ValueInfo) => Res) extends ((Env, Int => ValueInfo) => Res) {
    def apply(env: Env, valInfoFn: Int => ValueInfo): Res = fun(env, valInfoFn)
  }

  // TODO: add local context to ValueInfo and refactor Env
  //
  //   case class Context(syms: Map[Symbol, ValueInfo], parent: Context)
  //
  case class ValueInfo(partial: Boolean = false, latentInfo: LatentInfo = null) {
    def isLatent = latentInfo != null
  }

  class Env extends Cloneable {
    protected var _nonInit: Set[Symbol] = Set()
    protected var _partialSyms: Set[Symbol] = Set()
    protected var _lazyForced: Set[Symbol] = Set()
    protected var _latentSyms: Map[Symbol, LatentInfo] = Map()
    protected var _cls: ClassSymbol = null
    protected var _methChecking: Set[Symbol] = Set()

    def fresh: FreshEnv = this.clone.asInstanceOf[FreshEnv]

    def currentClass = _cls

    def isPartial(sym: Symbol)    = _partialSyms.contains(sym)
    def addPartial(sym: Symbol)   = _partialSyms += sym
    def removePartial(sym: Symbol)   = _partialSyms -= sym
    def partialSyms: Set[Symbol]  = _partialSyms

    def isLatent(sym: Symbol)     = _latentSyms.contains(sym)
    def addLatent(sym: Symbol, effs: LatentInfo) = _latentSyms += sym -> effs
    def latentInfo(sym: Symbol): LatentInfo = _latentSyms(sym)

    def isForced(sym: Symbol)     = _lazyForced.contains(sym)
    def addForced(sym: Symbol)    = _lazyForced += sym
    def lazyForced: Set[Symbol]   = _lazyForced

    def isNotInit(sym: Symbol)       = _nonInit.contains(sym)
    def addInit(sym: Symbol)      = _nonInit -= sym
    def nonInit: Set[Symbol]      = _nonInit

    def isChecking(sym: Symbol)   = _methChecking.contains(sym)
    def addChecking(sym: Symbol)  = _methChecking += sym
    def removeChecking(sym: Symbol) = _methChecking -= sym
    def checking[T](sym: Symbol)(fn: => T) = {
      addChecking(sym)
      val res = fn
      removeChecking(sym)
      res
    }

    def initialized: Boolean      = _nonInit.isEmpty && _partialSyms.size == 1
    def markInitialized           = {
      assert(initialized)
      _partialSyms = Set()
    }

    override def toString: String =
      s"""~------------ $currentClass -------------
          ~| not initialized:  ${_nonInit}
          ~| partial initialized: ${_partialSyms}
          ~| lazy forced:  ${_lazyForced}
          ~| latent symbols: ${_latentSyms.keys}"""
      .stripMargin('~')
  }

  class FreshEnv extends Env {
    def setPartialSyms(partialSyms: Set[Symbol]): this.type = { this._partialSyms = partialSyms; this }
    def setNonInit(nonInit: Set[Symbol]): this.type = { this._nonInit = nonInit; this }
    def setLazyForced(lazyForced: Set[Symbol]): this.type = { this._lazyForced = lazyForced; this }
    def setCurrentClass(cls: ClassSymbol): this.type = { this._cls = cls; this }
  }

  case class Res(val env: Env, var effects: Effects = Vector.empty, var valueInfo: ValueInfo = ValueInfo()) {

    def force(env: Env, valInfos: Int => ValueInfo): Res = if (isLatent) valueInfo.latentInfo(env, valInfos) else Res(env)
    def isLatent  = valueInfo.isLatent
    def isPartial = valueInfo.partial

    def +=(eff: Effect): Unit = effects = effects :+ eff
    def ++=(effs: Effects) = effects ++= effs

    def derived(effects: Effects = effects, valueInfo: ValueInfo = valueInfo, env: Env = env): Res =
      Res(env, effects, valueInfo)

    def join(res2: Res): Res = {
      val env3 = this.env.fresh
      env3.setNonInit(res2.env.nonInit ++ this.env.nonInit)
      env3.setLazyForced(res2.env.lazyForced ++ this.env.lazyForced)
      env3.setPartialSyms(res2.env.partialSyms ++ this.env.partialSyms)

      Res(
        env = env3,
        effects = res2.effects ++ this.effects,
        valueInfo = ValueInfo(
          partial = res2.isPartial || this.isPartial,
          latentInfo = LatentInfo {
            (env: Env, fn: Int => ValueInfo) => {
              val resA = this.force(env.fresh, fn)
              val resB = res2.force(env.fresh, fn)
              resA.join(resB)
            }
          }
        )
      )
    }

    override def toString: String =
      s"""~Res(
          ~|$env
          ~| effects = ${if (effects.isEmpty) "()" else effects.mkString("\n|    - ", "\n|    - ", "")}
          ~| partial = $isPartial
          ~| latent  = $isLatent
          ~)"""
      .stripMargin('~')
  }
}

class DataFlowChecker {

  import tpd._

  var depth: Int = 0
  val indentTab = " "

  def trace(msg: String)(body: => Res) = {
    indentedDebug(s"==> ${pad(msg)}?")
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

  def checkForce(sym: Symbol, tree: Tree, env: Env)(implicit ctx: Context): Res =
    if (sym.is(Lazy) && !env.isForced(sym)) {
      env.addForced(sym)
      val res = env.latentInfo(sym)(env, i => null)

      if (res.isPartial) res.env.addPartial(sym)
      if (res.isLatent) res.env.addLatent(sym, res.valueInfo.latentInfo)

      if (res.effects.nonEmpty) res.derived(effects = Vector(Force(sym, res.effects, tree.pos)))
      else res
    }
    else {
      val valueInfo = ValueInfo(
        partial = env.isPartial(sym),
        latentInfo = if (env.isLatent(sym)) env.latentInfo(sym) else null
      )
      Res(env = env, valueInfo = valueInfo)
    }

  def checkParams(sym: Symbol, paramInfos: List[Type], args: List[Tree], env: Env, force: Boolean)(implicit ctx: Context): (Res, Vector[ValueInfo]) = {
    def isParamPartial(index: Int) = paramInfos(index).hasAnnotation(defn.PartialAnnot)

    var effs = Vector.empty[Effect]
    var infos = Vector.empty[ValueInfo]
    var partial = false

    args.zipWithIndex.foreach { case (arg, index) =>
      val res = apply(env, arg)
      effs ++= res.effects
      partial = partial || res.isPartial
      infos = infos :+ res.valueInfo

      if (res.isLatent && force) {
        val effs2 = res.force(env, i => ValueInfo())            // latent values are not partial
        if (effs2.effects.nonEmpty) {
          partial = true
          if (!isParamPartial(index)) effs = effs :+ Latent(arg, effs2.effects)
        }
      }
      if (res.isPartial && !isParamPartial(index)) effs = effs :+ Argument(sym, arg)
    }

    (Res(env = env, effects = effs, valueInfo = ValueInfo(partial = partial)), infos)
  }

  def checkNew(tree: Tree, tref: TypeRef, init: TermRef, argss: List[List[tpd.Tree]], env: Env)(implicit ctx: Context): Res = {
    val paramInfos = init.widen.paramInfoss.flatten
    val args = argss.flatten

    val (res1, _) = checkParams(tref.symbol, paramInfos, args, env, force = true)

    if (!isPartial(tref.prefix, env) || isSafeParentAccess(tref, res1.env)) return res1

    if (!isLexicalRef(tref, res1.env)) {
      res1 += PartialNew(tref.prefix, tref.symbol, tree.pos)
      res1
    }
    else {
      val latentInfo = res1.env.latentInfo(tref.symbol)
      val res2 = latentInfo(res1.env, i => null)
      if (res2.effects.nonEmpty) res1 += Instantiate(tref.symbol, res2.effects, tree.pos)
      res1.derived(env = res2.env, valueInfo = ValueInfo(partial = true))
    }
  }

  def checkApply(tree: tpd.Tree, fun: Tree, args: List[Tree], env: Env)(implicit ctx: Context): Res = {
    val res1 = apply(env, fun)

    val paramInfos = fun.tpe.widen.asInstanceOf[MethodType].paramInfos
    val (res2, valueInfos) = checkParams(fun.symbol, paramInfos, args, res1.env, force = !res1.isLatent)

    var effs = res1.effects ++ res2.effects

    if (res1.isLatent) {
      val res3 = res1.force(res2.env, i => valueInfos(i))
      if (res3.effects.nonEmpty) effs = effs :+ Latent(tree, res3.effects)

      res3.derived(effects = effs)
    }
    else {
      Res(env = res2.env, effects = effs)
    }
  }

  def checkSelect(tree: Select, env: Env)(implicit ctx: Context): Res = {
    val res = apply(env, tree.qualifier)

    if (res.isPartial)
      res += Member(tree.symbol, tree.qualifier, tree.pos)

    res
  }

  /** return the top-level local term within `cls` refered by `tp`, NoType otherwise.
   *
   *  There are following cases:
   *   - select on this: `C.this.x`
   *   - select on super: `C.super[Q].x`
   *   - local ident: `x`
   *   - select on self: `self.x` (TODO)
   */
  def localRef(tp: Type, env: Env)(implicit ctx: Context): Type = tp match {
    case TermRef(ThisType(tref), _) if tref.symbol.isContainedIn(env.currentClass) => tp
    case TermRef(SuperType(ThisType(tref), _), _) if tref.symbol.isContainedIn(env.currentClass) => tp
    case ref @ TermRef(NoPrefix, _) if ref.symbol.isContainedIn(env.currentClass) => ref
    case TermRef(tp: TermRef, _) => localRef(tp, env)
    case _ => NoType
  }

  object NamedTypeEx {
    def unapply(tp: Type)(implicit ctx: Context): Option[(Type, Symbol)] = tp match {
      case ref: TermRef => Some(ref.prefix -> ref.symbol)
      case ref: TypeRef => Some(ref.prefix -> ref.symbol)
      case _ => None
    }
  }

  /** Does the NamedType refer to a symbol defined within `cls`? */
  def isLexicalRef(tp: NamedType, env: Env)(implicit ctx: Context): Boolean =
    ctx.owner.isContainedIn(tp.symbol.owner) || tp.symbol.isContainedIn(ctx.owner)

  /** Is the NamedType a reference to safe member defined in the parent of `cls`?
   *
   *  A member access is safe in the following cases:
   *  - a non-lazy, non-deferred field where the primary constructor takes no partial values
   *  - a method marked as `@init`
   *  - a class marked as `@init`
   */
  def isSafeParentAccess(tp: NamedType, env: Env)(implicit ctx: Context): Boolean =
    tp.symbol.owner.isClass && (env.currentClass.isSubClass(tp.symbol.owner) || env.currentClass.givenSelfType.classSymbols.exists(_.isSubClass(tp.symbol.owner))) &&
      (
        tp.symbol.isTerm && tp.symbol.is(AnyFlags, butNot = Method | Lazy | Deferred) && !hasPartialParam(tp.symbol.owner, env) ||
        tp.symbol.hasAnnotation(defn.InitAnnot) || tp.symbol.hasAnnotation(defn.PartialAnnot) ||
        isDefaultGetter(tp.symbol) || (env.initialized && env.currentClass.is(Final))
      )

  // TODO: default methods are not necessarily safe, if they call other methods
  def isDefaultGetter(sym: Symbol)(implicit ctx: Context) = sym.name.is(NameKinds.DefaultGetterName)

  def hasPartialParam(clazz: Symbol, env: Env)(implicit ctx: Context): Boolean =
    env.currentClass.paramAccessors.exists(_.hasAnnotation(defn.PartialAnnot))

  def isPartial(tp: Type, env: Env)(implicit ctx: Context): Boolean = tp match {
    case tmref: TermRef             => env.isPartial(tmref.symbol)
    case ThisType(tref)             => env.isPartial(tref.symbol)
    case SuperType(thistp, _)       => isPartial(thistp, env)        // super is partial if `thistp` is partial
    case _                          => false
  }

  def checkTermRef(tree: Tree, env: Env)(implicit ctx: Context): Res = {
    indentedDebug(s"is ${tree.show} local ? = " + localRef(tree.tpe, env).exists)
    val ref: TermRef = localRef(tree.tpe, env) match {
      case NoType         => return Res(env = env)
      case tmref: TermRef => tmref
    }

    val sym = ref.symbol

    var effs = Vector.empty[Effect]

    if (isLexicalRef(ref, env)) {
      if (env.isNotInit(sym)) effs = effs :+ Uninit(sym, tree.pos)

      if (sym.is(Lazy)) {                // a forced lazy val could be partial and latent
        val res2 = checkForce(sym, tree, env)
        return res2.derived(effects = effs ++ res2.effects)
      }
      else if (sym.is(Method)) {
        if (!(sym.hasAnnotation(defn.InitAnnot) || sym.isEffectivelyFinal || isDefaultGetter(sym)))
          effs = effs :+ OverrideRisk(sym, tree.pos)

        if (sym.info.isInstanceOf[ExprType]) {       // parameter-less call
          val latentInfo = env.latentInfo(sym)
          val res2 = latentInfo(env, i => null)

          return {
            if (res2.effects.nonEmpty) res2.derived(effects = Vector(Call(sym, effs ++ res2.effects, tree.pos)))
            else res2.derived(effects = effs)
          }
        }
        else {
          return Res(env = env, effects = effs, valueInfo = ValueInfo(false, env.latentInfo(sym)))
        }
      }
      else if (sym.is(Deferred) && !sym.hasAnnotation(defn.InitAnnot) && sym.owner == env.currentClass) {
        effs = effs :+ UseAbstractDef(sym, tree.pos)
      }
    }
    else if (isPartial(ref.prefix, env) && !isSafeParentAccess(ref, env)) {
      effs = effs :+ Member(sym, tree, tree.pos)
    }

    Res(
      effects = effs, env = env,
      valueInfo = ValueInfo(
        partial = env.isPartial(sym),
        latentInfo = if (env.isLatent(sym)) env.latentInfo(sym) else null
      )
    )
  }

  def checkClosure(sym: Symbol, tree: Tree, env: Env)(implicit ctx: Context): Res = {
    Res(
      env = env,
      valueInfo = ValueInfo(
        partial = false,
        latentInfo = env.latentInfo(sym)
      )
    )
  }

  def checkIf(tree: If, env: Env)(implicit ctx: Context): Res = {
    val If(cond, thenp, elsep) = tree

    val res1: Res = apply(env, cond)
    val res2: Res = apply(res1.env.fresh, thenp)
    val res3: Res = apply(res1.env.fresh, elsep)

    res2.derived(effects = res1.effects ++ res2.effects).join(res3)
  }

  def checkValDef(vdef: ValDef, env: Env)(implicit ctx: Context): Res = {
    val res1 = apply(env, vdef.rhs)

    if (!tpd.isWildcardArg(vdef.rhs) && !vdef.rhs.isEmpty) res1.env.addInit(vdef.symbol)  // take `_` as uninitialized, otherwise it's initialized

    if (res1.isPartial) {
      if (res1.env.initialized) // fully initialized
        res1.env.markInitialized
      else
        res1.env.addPartial(vdef.symbol)
    }

    if (res1.isLatent)
      res1.env.addLatent(vdef.symbol, res1.valueInfo.latentInfo)

    res1.valueInfo = ValueInfo()

    res1
  }

  def checkBlock(tree: Block, env: Env)(implicit ctx: Context): Res = {
    indexLatents(tree.stats, env)

    val res = tree.stats.foldLeft(Res(env = env)) { (acc, stat) =>
      indentedDebug(s"acc = ${pad(acc.toString)}")
      val res1 = apply(acc.env, stat)
      acc.derived(env = res1.env, effects = acc.effects ++ res1.effects)
    }

    val res1 = apply(res.env, tree.expr)

    res1.derived(effects = res.effects ++ res1.effects)
  }

  def indexLatents(stats: List[Tree], env: Env)(implicit ctx: Context): Unit = stats.foreach {
    case ddef: DefDef if ddef.symbol.is(AnyFlags, butNot = Accessor) =>
      // TODO: multiple calls & capturing of params, split Env to context-sensitive & context-insensitive
      val (init: List[List[ValDef]], last: List[ValDef]) = ddef.vparamss match {
        case Nil => (Nil, Nil)
        case init :+ last => (init, last)
      }
      val zero = LatentInfo { (env, valInfoFn) =>
        if (env.isChecking(ddef.symbol)) {
          debug(s"recursive call found during initialization of ${ddef.symbol}")
          Res(env)
        }
        else {
          if (last.nonEmpty) {
            last.zipWithIndex.foreach { case (param: ValDef, index: Int) =>
              val paramInfo = valInfoFn(index)
              if (paramInfo.isLatent) env.addLatent(param.symbol, paramInfo.latentInfo)
              if (paramInfo.partial) env.addPartial(param.symbol)
            }
          }
          env.checking(ddef.symbol) { apply(env, ddef.rhs)(ctx.withOwner(ddef.symbol)) }
        }
      }

      val latentInfo = init.foldRight(zero) { (params, latentInfo) =>
        LatentInfo { (env, valInfoFn) =>
          params.zipWithIndex.foreach { case (param, index) =>
            val paramInfo = valInfoFn(index)
            if (paramInfo.isLatent) env.addLatent(param.symbol, paramInfo.latentInfo)
            if (paramInfo.partial) env.addPartial(param.symbol)
          }

          Res(env = env, valueInfo = ValueInfo(latentInfo = latentInfo))
        }
      }
      env.addLatent(ddef.symbol, latentInfo)
    case vdef: ValDef if vdef.symbol.is(Lazy)  =>
      val latent = LatentInfo { (env, valInfoFn) =>
        if (env.isChecking(vdef.symbol)) {
          debug(s"recursive call found during initialization of ${vdef.symbol}")
          Res(env)
        }
        else env.checking(vdef.symbol) {
          apply(env, vdef.rhs)
        }
      }
      env.addLatent(vdef.symbol, latent)
    case tdef: TypeDef if tdef.isClassDef  =>
      val latent = LatentInfo { (env, valInfoFn) =>
        if (env.isChecking(tdef.symbol)) {
          debug(s"recursive call found during initialization of ${tdef.symbol}")
          Res(env)
        }
        else env.checking(tdef.symbol) {
          apply(env, tdef.rhs)(ctx.withOwner(tdef.symbol))
        }
      }
      env.addLatent(tdef.symbol, latent)
    case _ =>
  }

  def apply(env: Env, tree: Tree)(implicit ctx: Context): Res = trace("checking " + tree.show)(tree match {
    case tmpl: Template =>
      val stats = tmpl.body.filter {
        case vdef : ValDef  =>
          !vdef.symbol.hasAnnotation(defn.ScalaStaticAnnot)
        case stat =>
          true
      }
      apply(env, Block(stats, tpd.unitLiteral))
    case vdef : ValDef if !vdef.symbol.is(Lazy) =>
      checkValDef(vdef, env)
    case _: DefTree =>  // ignore other definitions
      Res(env = env)
    case Closure(_, meth, _) =>
      checkClosure(meth.symbol, tree, env)
    case tree: Ident if tree.symbol.isTerm =>
      checkTermRef(tree, env)
    case tree @ Select(prefix @ (This(_) | Super(_, _)), _) if tree.symbol.isTerm =>
      checkTermRef(tree, env)
    case tree @ NewEx(tref, init, argss) =>
      checkNew(tree, tref, init, argss, env)
    case tree @ Select(prefix, _) if tree.symbol.isTerm =>
      checkSelect(tree, env)
    case tree @ This(_) =>
      if (env.isPartial(tree.symbol) && !env.initialized) Res(env = env, valueInfo = ValueInfo(partial = true))
      else Res(env = env)
    case tree @ Super(qual, mix) =>
      if (env.isPartial(qual.symbol) && !env.initialized) Res(env = env, valueInfo = ValueInfo(partial = true))
      else Res(env = env)
    case tree @ If(cond, thenp, elsep) =>
      checkIf(tree, env)
    case tree @ Apply(fun, args) =>
      checkApply(tree, fun, args, env)
    case tree @ Assign(lhs @ (Ident(_) | Select(This(_), _)), rhs) =>
      val resRhs = apply(env, rhs)

      if (!resRhs.isPartial || env.isPartial(lhs.symbol) || env.isNotInit(lhs.symbol)) {
        resRhs.env.addInit(lhs.symbol)
        if (!resRhs.isPartial) resRhs.env.removePartial(lhs.symbol)
        else resRhs.env.addPartial(lhs.symbol)
      }
      else resRhs += CrossAssign(lhs, rhs)

      resRhs.valueInfo = ValueInfo()

      resRhs
    case tree @ Assign(lhs @ Select(prefix, _), rhs) =>
      val resLhs = apply(env, prefix)
      val resRhs = apply(resLhs.env, rhs)

      val res = Res(env = resRhs.env, effects = resLhs.effects ++ resRhs.effects)

      if (resRhs.isPartial && !resLhs.isPartial)
        res += CrossAssign(lhs, rhs)

      res
    case tree @ Block(stats, expr) =>
      checkBlock(tree, env)
    case Typed(expr, tpd) =>
      apply(env, expr)
    case _ =>
      Res(env = env)
  })
}