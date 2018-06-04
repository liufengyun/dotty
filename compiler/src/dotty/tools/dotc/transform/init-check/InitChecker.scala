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
 *  TODO:
 *   - parent call abstract methods during initialization
 *      - scala/tools/nsc/backend/jvm/BackendInterface.scala:722
 *      - scala/tools/nsc/backend/jvm/BCodeBodyBuilder.scala:1451
 *      - scala/tools/nsc/backend/jvm/BackendInterface.scala:727
 *      - compiler/src/dotty/tools/dotc/config/Properties.scala:23
 *      - compiler/src/dotty/tools/dotc/config/Properties.scala:69
 *      - compiler/src/dotty/tools/dotc/core/Denotations.scala:1162
 *      - compiler/src/dotty/tools/io/AbstractFile.scala:97
 *   - child call parent method during initialization
 *      - compiler/src/dotty/tools/dotc/config/ScalaSettings.scala:16
 *      - compiler/src/dotty/tools/dotc/ast/DesugarEnums.scala:19
 *      - compiler/src/dotty/tools/dotc/core/Contexts.scala:573
 *      - compiler/src/dotty/tools/dotc/core/StdNames.scala:63
 *      - compiler/src/dotty/tools/dotc/core/unpickleScala2/Scala2Unpickler.scala:236
 *      - compiler/src/dotty/tools/dotc/interactive/InteractiveDriver.scala:34
 *      - compiler/src/dotty/tools/dotc/parsing/JavaTokens.scala:18
 *      - compiler/src/dotty/tools/dotc/typer/Applications.scala:546
 *   - select field of parent
 *      - compiler/src/dotty/tools/dotc/ast/Desugar.scala:82
 *      - compiler/src/dotty/tools/dotc/core/Contexts.scala:573
 *      - compiler/src/dotty/tools/dotc/core/Comments.scala:120
 *      - compiler/src/dotty/tools/dotc/core/tasty/TreeBuffer.scala:14
 *   - `this` escape as full value
 *      - compiler/src/dotty/tools/dotc/Run.scala:61
 *      - compiler/src/dotty/tools/dotc/core/Contexts.scala:552
 *      - compiler/src/dotty/tools/dotc/core/Types.scala:2353
 *      - compiler/src/dotty/tools/dotc/core/Types.scala:3054
 *      - compiler/src/dotty/tools/dotc/core/Types.scala:3073
 *      - compiler/src/dotty/tools/dotc/core/tasty/TastyPickler.scala:73
 *      - compiler/src/dotty/tools/dotc/typer/RefChecks.scala:851
 *   - `this` escape in a partial closure
 *      - compiler/src/dotty/tools/dotc/core/Definitions.scala:855
 *      - compiler/src/dotty/tools/dotc/transform/LambdaLift.scala:354
 *      - compiler/src/dotty/tools/dotc/transform/MegaPhase.scala:402
 *   - init methods not final or private
 *      - compiler/src/dotty/tools/dotc/ast/Positioned.scala:118
 *      - compiler/src/dotty/tools/dotc/ast/Positioned.scala:54
 *      - compiler/src/dotty/tools/dotc/parsing/CharArrayReader.scala:10
 *      - compiler/src/dotty/tools/dotc/parsing/JavaScanners.scala:534
 *   - `this` escape in val overriding method
 *      - compiler/src/dotty/tools/dotc/core/Contexts.scala:538
 *   - create instance of nested class
 *      - compiler/src/dotty/tools/dotc/core/NameKinds.scala:68
 *   - fix me
 *      - compiler/src/dotty/tools/dotc/core/NameKinds.scala:88
 *      - compiler/src/dotty/tools/dotc/core/SymDenotations.scala:1355
 *      - compiler/src/dotty/tools/dotc/reporting/diagnostic/messages.scala:1342 default methods
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

    val env: Res = (new FreshEnv).setNonInit(noninit).setPartialSyms(partial).setCurrentClass(cls)
    val checker = new DataFlowChecker

    val res = checker(env, tree)
    res.effects.foreach(_.report)
    res.nonInit.foreach { sym =>
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
  type LatentEffects = Res => Vector[Effect]
  // TODO: handle curried functions & methods uniformly
  // type LatentEffects = Env => (Vector[Effect], LatentEffects)

  class Env extends Cloneable {
    protected var _nonInit: Set[Symbol] = Set()
    protected var _partialSyms: Set[Symbol] = Set()
    protected var _lazyForced: Set[Symbol] = Set()
    protected var _latentSyms: Map[Symbol, LatentEffects] = Map()
    protected var _cls: ClassSymbol = null
    protected var _defns: Map[Symbol, tpd.Tree] = Map()
    protected var _methChecking: Set[Symbol] = Set()

    def fresh: FreshEnv = this.clone.asInstanceOf[FreshEnv].noRes

    def currentClass = _cls

    def isPartial(sym: Symbol)    = _partialSyms.contains(sym)
    def addPartial(sym: Symbol)   = _partialSyms += sym
    def removePartial(sym: Symbol)   = _partialSyms -= sym
    def partialSyms: Set[Symbol]  = _partialSyms

    def isLatent(sym: Symbol)     = _latentSyms.contains(sym)
    def addLatent(sym: Symbol, effs: LatentEffects) = _latentSyms += sym -> effs
    def latentEffects(sym: Symbol): LatentEffects = _latentSyms(sym)

    def isForced(sym: Symbol)     = _lazyForced.contains(sym)
    def addForced(sym: Symbol)    = _lazyForced += sym
    def lazyForced: Set[Symbol]   = _lazyForced

    def isNotInit(sym: Symbol)       = _nonInit.contains(sym)
    def addInit(sym: Symbol)      = _nonInit -= sym
    def nonInit: Set[Symbol]      = _nonInit

    def isChecking(sym: Symbol)   = _methChecking.contains(sym)
    def addChecking(sym: Symbol)  = _methChecking += sym
    def removeChecking(sym: Symbol) = _methChecking -= sym
    def checking(sym: Symbol)(fn: => Unit) = {
      addChecking(sym)
      fn
      removeChecking(sym)
    }

    def initialized: Boolean      = _nonInit.isEmpty && _partialSyms.size == 1
    def markInitialized           = {
      assert(initialized)
      _partialSyms = Set()
    }

    def addDef(sym: Symbol, tree: tpd.Tree) = _defns += sym -> tree
    def removeDef(sym: Symbol)    = _defns -= sym
    def addDefs(defs: List[(Symbol, tpd.Tree)]) = _defns ++= defs
    def removeDefs(defs: List[Symbol]) = _defns --= defs
    def defn(sym: Symbol)         = _defns(sym)
  }

  // TODO: change Env to be a field of Res
  class Res extends Env {
    var effects: Effects = Vector.empty
    var partial: Boolean = false
    var latentEffects: LatentEffects = null

    def force(env: Res): Effects = latentEffects(env)
    def isLatent = latentEffects != null

    def +=(eff: Effect): Unit = effects = effects :+ eff
    def ++=(effs: Effects) = effects ++= effs

    def propagate(res: Res, withEffs: Boolean = true) = {
      this._nonInit = res._nonInit
      this._lazyForced = res._lazyForced
      if (withEffs) this.effects ++= res.effects
      this.partial = res.partial
      this.latentEffects = res.latentEffects
    }

    def noRes: this.type = {
      effects = Vector.empty
      partial = false
      latentEffects = null

      this
    }

    def diagnose(implicit ctx: Context) = {
      debug(s"------------ $currentClass ------------->")
      debug("not initialized: " + _nonInit)
      debug("partial initialized: " + _partialSyms)
      debug("lazy forced: " + _lazyForced)
      debug("latent symbols: " + _latentSyms.keys)
      debug(s"<--------------------------------")
    }

    def show(implicit ctx: Context) = {
      println(s"------------ $currentClass ------------->")
      println("not initialized: " + _nonInit)
      println("partial initialized: " + _partialSyms)
      println("lazy forced: " + _lazyForced)
      println("latent symbols: " + _latentSyms.keys)
      println(s"<--------------------------------")
    }
  }

  class FreshEnv extends Res {
    def setPartialSyms(partialSyms: Set[Symbol]): this.type = { this._partialSyms = partialSyms; this }
    def setNonInit(nonInit: Set[Symbol]): this.type = { this._nonInit = nonInit; this }
    def setLazyForced(lazyForced: Set[Symbol]): this.type = { this._lazyForced = lazyForced; this }
    def setCurrentClass(cls: ClassSymbol): this.type = { this._cls = cls; this }
  }
}

class DataFlowChecker extends tpd.TreeAccumulator[Res] {

  import tpd._

  def checkForce(sym: Symbol, tree: Tree, env: Res)(implicit ctx: Context) =
    if (sym.is(Lazy) && !env.isForced(sym)) {
      env.addForced(sym)
      val rhs = env.defn(sym)
      val env2 = apply(env.fresh, rhs)

      if (env2.effects.nonEmpty) env += Force(sym, env2.effects, tree.pos)

      env.propagate(env2, withEffs = false)
    }

  def checkCall(fun: TermRef, tree: Tree, env: Res)(implicit ctx: Context): Res = {
    val sym = fun.symbol
    debug("checking call " + sym)
    if (env.isChecking(sym)) {
      debug("recursive call found during initialization")
    }
    else {
      if (!(sym.hasAnnotation(defn.InitAnnot) || sym.isEffectivelyFinal || isDefaultGetter(sym)))
        env += OverrideRisk(sym, tree.pos)

      env.checking(sym) {
        val rhs = env.defn(sym)
        val env2 = apply(env.fresh, rhs)

        env.propagate(env2, withEffs = false)

        if (env2.effects.nonEmpty) env += Call(sym, env2.effects, tree.pos)
      }
    }

    env
  }

  def checkParams(sym: Symbol, paramInfos: List[Type], args: List[Tree], env: Res)(implicit ctx: Context) = {
    def isParamPartial(index: Int) = paramInfos(index).hasAnnotation(defn.PartialAnnot)

    args.zipWithIndex.foreach { case (arg, index) =>
      val env2 = apply(env.fresh, arg)
      env.propagate(env2)
      env.partial |= env2.partial


      if (env2.isLatent) {
        val effs = env2.latentEffects(env.fresh)                   // latent values are not partial
        if (effs.nonEmpty) {
          env.partial = true
          if (!isParamPartial(index)) env += Latent(arg, effs)
        }
      }
      else if (env2.partial && !isParamPartial(index)) env += Argument(sym, arg)
    }
  }

  def checkNew(tree: Tree, tref: TypeRef, init: TermRef, argss: List[List[tpd.Tree]], env: Res)(implicit ctx: Context): Res = {
    val paramInfos = init.widen.paramInfoss.flatten
    val args = argss.flatten

    env.partial = false
    checkParams(tref.symbol, paramInfos, args, env)

    if (!isPartial(tref.prefix, env) || isSafeParentAccess(tref, env)) return env

    if (!isLexicalRef(tref, env))
      env += PartialNew(tref.prefix, tref.symbol, tree.pos)
    else {
      if (env.isChecking(tref.symbol)) {
        debug("recursive call found during initialization")
      }
      else env.checking(tref.symbol) {
        val tmpl = env.defn(tref.symbol)
        val env2 = apply(env.fresh, tmpl)
        if (env2.effects.nonEmpty) env += Instantiate(tref.symbol, env2.effects, tree.pos)
      }
    }

    env
  }

  def checkApply(tree: tpd.Tree, fun: Tree, args: List[Tree], env: Res)(implicit ctx: Context): Res = {
    val env2 = apply(env.fresh, fun)
    env.propagate(env2)

    val paramInfos = fun.tpe.widen.asInstanceOf[MethodType].paramInfos

    checkParams(fun.symbol, paramInfos, args, env)
    env.partial = false
    env.latentEffects = null

    // function apply: see TODO for LatentEffects
    if (env2.isLatent) {
      val effs = env2.latentEffects(env)
      if (effs.nonEmpty) env += Latent(tree, effs)
    }

    if (!tree.tpe.isInstanceOf[MethodOrPoly]) {     // check when fully applied
      val mt = methPart(tree)
      mt.tpe match {
        case ref: TermRef if isPartial(ref.prefix, env) && isLexicalRef(ref, env) =>
          checkCall(ref, tree, env)
        case _ =>
      }
    }

    env
  }

  def checkSelect(tree: Select, env: Res)(implicit ctx: Context): Res = {
    apply(env, tree.qualifier)

    if (env.partial)
      env += Member(tree.symbol, tree.qualifier, tree.pos)

    env
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
    case tmref @ TermRef(NoPrefix, _) if tmref.symbol.isContainedIn(env.currentClass) => tmref
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
    tp.symbol.isContainedIn(env.currentClass)

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

  def isPartial(tp: Type, env: Res)(implicit ctx: Context): Boolean = tp match {
    case tmref: TermRef             => env.isPartial(tmref.symbol)
    case ThisType(tref)             => env.isPartial(tref.symbol)
    case SuperType(thistp, _)       => isPartial(thistp, env)        // super is partial if `thistp` is partial
    case _                          => false
  }

  def checkTermRef(tree: Tree, env: Res)(implicit ctx: Context): Res = {
    val ref: TermRef = localRef(tree.tpe, env) match {
      case NoType         => return env
      case tmref: TermRef => tmref
    }

    if (env.isPartial(ref.symbol)) env.partial = true
    if (env.isLatent(ref.symbol)) env.latentEffects = env.latentEffects(ref.symbol)

    if (isLexicalRef(ref, env)) {
      if (env.isNotInit(ref.symbol)) env += Uninit(ref.symbol, tree.pos)

      if (ref.symbol.is(Lazy))
        checkForce(ref.symbol, tree, env)
      else if (ref.symbol.is(Method) && ref.symbol.info.isInstanceOf[ExprType]) // parameter-less call
        checkCall(ref, tree, env)
      else if (ref.symbol.is(Deferred) && !ref.symbol.hasAnnotation(defn.InitAnnot) && ref.symbol.owner == env.currentClass)
        env += UseAbstractDef(ref.symbol, tree.pos)
    }
    else if (isPartial(ref.prefix, env) && !isSafeParentAccess(ref, env))
      env += Member(ref.symbol, tree, tree.pos)

    env
  }

  def checkClosure(sym: Symbol, tree: Tree, env: Res)(implicit ctx: Context): Res = {
    val body = env.defn(sym)
    debug("checking closure: " + body.show)
    env.latentEffects = (env: Res) => apply(env, body).effects
    env.partial = false
    env
  }

  def checkIf(tree: If, env: Res)(implicit ctx: Context): Res = {
    val If(cond, thenp, elsep) = tree

    apply(env, cond)
    val env1 = apply(env.fresh, thenp)
    val env2 = apply(env.fresh, elsep)

    val res = env.fresh
    res.setNonInit(env1.nonInit ++ env2.nonInit)
    res.setLazyForced(env1.lazyForced ++ env2.lazyForced)
    res.setPartialSyms(env1.partialSyms ++ env2.partialSyms)

    res.effects = env.effects ++ env1.effects ++ env2.effects
    res.partial = env1.partial || env2.partial
    res.latentEffects = (env: Res) => env1.force(env.fresh) ++ env2.force(env.fresh)

    res
  }

  def apply(env: Res, tree: Tree)(implicit ctx: Context) = tree match {
    case tmpl: Template =>
      val stats = tmpl.body.filter {
        case vdef : ValDef  =>
          !vdef.symbol.hasAnnotation(defn.ScalaStaticAnnot)
        case stat =>
          true
      }
      apply(env, Block(stats, tpd.unitLiteral))
    case vdef : ValDef if !vdef.symbol.is(Lazy) =>
      val env2 = apply(env, vdef.rhs)

      if (!tpd.isWildcardArg(vdef.rhs) && !vdef.rhs.isEmpty) env2.addInit(vdef.symbol)  // take `_` as uninitialized, otherwise it's initialized

      if (env2.partial) {
        if (env2.initialized) // fully initialized
          env2.markInitialized
        else
          env2.addPartial(vdef.symbol)
      }

      if (env2.isLatent)
        env2.addLatent(vdef.symbol, env2.latentEffects)

      env2.latentEffects = null

      env2
    case _: DefTree =>  // ignore other definitions
      env
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
      if (env.isPartial(tree.symbol) && !env.initialized) env.partial = true
      env
    case tree @ Super(qual, mix) =>
      if (env.isPartial(qual.symbol) && !env.initialized) env.partial = true
      env
    case tree @ If(cond, thenp, elsep) =>
      checkIf(tree, env)
    case tree @ Apply(fun, args) =>
      checkApply(tree, fun, args, env)
    case tree @ Assign(lhs @ (Ident(_) | Select(This(_), _)), rhs) =>
      apply(env, rhs)

      if (!env.partial || env.isPartial(lhs.symbol) || env.isNotInit(lhs.symbol)) {
        env.addInit(lhs.symbol)
        if (!env.partial) env.removePartial(lhs.symbol)
        else env.addPartial(lhs.symbol)
      }
      else env += CrossAssign(lhs, rhs)

      env.latentEffects = null
      env.partial = false

      env
    case tree @ Assign(lhs @ Select(prefix, _), rhs) =>
      val env1 = apply(env.fresh, prefix)
      val env2 = apply(env.fresh, rhs)
      env.propagate(env1)
      env.propagate(env2)

      if (env2.partial && !env1.partial)
        env += CrossAssign(lhs, rhs)

      env.latentEffects = null
      env.partial = false

      env
    case tree @ Block(stats, expr) =>
      val meths = stats.collect {
        case ddef: DefDef if ddef.symbol.is(AnyFlags, butNot = Accessor) =>
          ddef.symbol -> ddef.rhs
        case vdef: ValDef if vdef.symbol.is(Lazy)  =>
          vdef.symbol -> vdef.rhs
        case tdef: TypeDef if tdef.isClassDef  =>
          tdef.symbol -> tdef.rhs
      }
      debug("local methods: " + meths.map(_._1))

      env.addDefs(meths)
      val res = foldOver(env, tree)
      env.removeDefs(meths.map(_._1))

      res
    case _ =>
      foldOver(env, tree)
  }
}