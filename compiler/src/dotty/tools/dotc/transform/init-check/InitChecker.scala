package dotty.tools.dotc
package transform

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

import DataFlowChecker._

object InitChecker {
  val name = "initChecker"

  def isPartial(sym: Symbol)(implicit ctx: Context) = sym.info.hasAnnotation(defn.PartialAnnot)

  def isFilled(sym: Symbol)(implicit ctx: Context) = sym.info.hasAnnotation(defn.FilledAnnot)

  def isConcreteField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Deferred | Method | Local | Private)

  def isNonParamField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Method | ParamAccessor | Lazy | Deferred)

  def isField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Method | Lazy | Deferred)

  def createRootEnv: Env = {
    val heap = new Heap
    val env = new Env(-1)
    heap.addEnv(heap)
    env
  }

  def setupClassEnv(env: FreshEnv, cls: ClassSymbol)(implicit ctx: Context) = {
    val accessors = cls.paramAccessors.filterNot(x => x.isSetter)

    var noninit = Set[Symbol]()    // definitions that are not initialized
    var partial = Set[Symbol]()    // definitions that are partial initialized

    // partial fields of current class
    for (param <- accessors if isPartial(param)) partial += param

    // partial fields of super class
    for (
      parent <- cls.baseClasses.tail;
      decl <- parent.info.decls.toList
      if isConcreteField(decl) && isPartial(decl)
    )
    partial += decl

    // non-initialized fields of current class
    for (decl <- cls.info.decls.toList if isNonParamField(decl))
    noninit += decl

    env.setNonInit(noninit).setPartialSyms(partial).setLocals(noninit ++ partial)
  }

  def setupMethodEnv(env: FreshEnv, cls: ClassSymbol, meth: Symbol, isOverriding: Boolean)(implicit ctx: Context) = {
    val accessors = cls.paramAccessors.filterNot(x => x.isSetter)

    var noninit = Set[Symbol]()    // definitions that are not initialized
    var partial = Set[Symbol]()    // definitions that are partial initialized

    // partial fields of current class
    for (param <- accessors if isPartial(param)) partial += param

    // partial fields of super class
    for (
      parent <- cls.baseClasses.tail;
      decl <- parent.info.decls.toList
      if isConcreteField(decl) && isPartial(decl)
    )
    partial += decl

    // non-initialized fields of current class
    if (cls.is(Trait))
      for (decl <- cls.info.decls.toList if isField(decl))
      noninit += decl
    else if (isOverriding)
      for (decl <- cls.info.decls.toList if isNonParamField(decl))
      noninit += decl

    env.setNonInit(noninit)
    env.setPartialSyms(partial)
    env.setLocals(noninit ++ partial)
  }
}

/** This transform checks initialization is safe based on data-flow analysis
 *
 *  - Partial
 *  - Filled
 *  - Full
 *
 *  1. A _full_ object is fully initialized.
 *  2. All fields of a _filled_ object are assigned, but the fields may refer to non-full objects.
 *  3. A _partial_ object may have unassigned fields.
 *
 *  TODO:
 *   - check default arguments of init methods
 *   - selection on ParamAccessors of partial value is fine if the param is not partial
 *   - handle tailrec calls during initialization (which captures `this`)
 */
class InitChecker extends MiniPhase with IdentityDenotTransformer { thisPhase =>
  import tpd._, InitChecker._

  override def phaseName: String = InitChecker.name

  override def transformDefDef(ddef: tpd.DefDef)(implicit ctx: Context): tpd.Tree = {
    val sym = ddef.symbol
    val overrideInit = sym.allOverriddenSymbols.exists(_.hasAnnotation(defn.InitAnnot))

    if (overrideInit ||sym.hasAnnotation(defn.InitAnnot)) {
      val cls = sym.owner.asClass
      val root = createRootEnv

      val classEnv = setupMethodEnv(root.newEnv, sym.owner.asClass, sym, isOverriding = overrideInit)
      val thisInfo = new ObjectEnv(classEnv.id)

      root.setPartialSyms(Set(cls))
      root.setLatentSyms(Map(cls -> thisInfo))

      val checker = new DataFlowChecker

      val res = checker.apply(ddef.rhs, classEnv)
      res.effects.foreach(_.report)
      if (res.effects.nonEmpty) ctx.warning(s"init $sym may cause initialization problems", ddef.pos)
    }

    ddef
  }

  override def transformTemplate(tree: Template)(implicit ctx: Context): Tree = {
    val cls = ctx.owner.asClass
    val self = cls.thisType

    if (cls.hasAnnotation(defn.UncheckedAnnot)) return tree

    def lateInitMsg(sym: Symbol) =
      s"""|Initialization too late: $sym may be used during parent initialization.
          |Consider make it a class parameter."""
        .stripMargin

    for (decl <- cls.info.decls.toList if decl.is(AnyFlags, butNot = Method | Deferred)) {
      val overrideInit = decl.allOverriddenSymbols.exists(_.hasAnnotation(defn.InitAnnot))
      if (overrideInit && !decl.is(ParamAccessor | Override))
        ctx.warning(lateInitMsg(decl), decl.pos)
    }

    var membersToCheck: util.SimpleIdentityMap[Name, Type] = util.SimpleIdentityMap.Empty[Name]
    val seenClasses = new util.HashSet[Symbol](256)

    def parents(cls: Symbol) =
      cls.info.parents.map(_.classSymbol)
        .filter(_.is(AbstractOrTrait))
        .dropWhile(_.is(JavaDefined | Scala2x))

    def addDecls(cls: Symbol): Unit =
      if (!seenClasses.contains(cls)) {
        seenClasses.addEntry(cls)
        for (mbr <- cls.info.decls)
          if (mbr.isTerm && mbr.is(Deferred | Method) &&
              (mbr.hasAnnotation(defn.PartialAnnot) || mbr.hasAnnotation(defn.FilledAnnot)) &&
              !membersToCheck.contains(mbr.name))
            membersToCheck = membersToCheck.updated(mbr.name, mbr.info.asSeenFrom(self, mbr.owner))
          parents(cls).foreach(addDecls)
      }
    parents(cls).foreach(addDecls)  // no need to check methods defined in current class

    def invalidImplementMsg(sym: Symbol) =
      s"""|@scala.annotation.partial required for ${sym.show} in ${sym.owner.show}
          |Because the abstract method it implements is marked as `@partial` or `@filled`."""
        .stripMargin

    for (name <- membersToCheck.keys) {
      val tp  = membersToCheck(name)
      for {
        mbrd <- self.member(name).alternatives
        if mbrd.info.overrides(tp, matchLoosely = true)
      } {
        val mbr = mbrd.symbol
        if (mbr.owner.ne(cls) && !mbr.hasAnnotation(defn.PartialAnnot))
          ctx.warning(invalidImplementMsg(mbr), cls.pos)
      }
    }

    val checker = new DataFlowChecker

    // current class env needs special setup
    val root = createRootEnv

    val classEnv = setupClassEnv(root.newEnv(), cls)
    checker.indexStats(tree.body, classEnv)
    val thisInfo = new ObjectEnv(classEnv.id)

    root.setPartialSyms(Set(cls))
    root.setLatentSyms(Map(cls -> thisInfo))

    val res = checker.checkStats(tree.body, classEnv)
    res.effects.foreach(_.report)
    classEnv.nonInit.foreach { sym =>
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
        ctx.warning(s"`@scala.annotation.init` is recommended for $sym for safe overriding", sym.pos)
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
      case RecCreate(cls, tree)  =>
        ctx.warning(s"Possible recursive creation of instance for ${cls.show}", tree.pos)
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
  case class RecCreate(cls: Symbol, tree: tpd.Tree) extends Effect                     // recursive creation of class

  type Effects = Vector[Effect]
  sealed trait LatentInfo {
    def asMethod: MethodInfo = this.asInstanceOf[MethodInfo]
    def asObject: ObjectInfo = this.asInstanceOf[ObjectInfo]
    def isMethod: Boolean = this.isInstanceOf[MethodInfo]
    def isObject: Boolean = !isMethod

    def join(other: LatentInfo): LatentInfo = (this, other) match {
      case (NoLatent, _) => other
      case (_, NoLatent) => this
      case (m1: MethodInfo, m2: MethodInfo) =>
        MethodInfo {
          (fn: Int => ValueInfo, heap: Heap) => {
            val resA = m1.apply(fn, heap)
            val resB = m2.apply(fn, heap)
            resA.join(resB)
          }
        }
      case (o1: ObjectInfo, o2: ObjectInfo) =>
        ObjectInfo {
          (sym: Symbol, heap: Heap) => {
            val resA = this.select(sym, heap)
            val resB = other.select(sym, heap)
            resA.join(resB)
          }
        }
      case _ =>
        throw new Exception(s"Can't join $this and $other")
    }
  }

  object NoLatent extends LatenInfo

  case class MethodInfo(fun: (Int => ValueInfo, Heap) => Res) extends LatentInfo {
    def apply(valInfoFn: Int => ValueInfo, heap: Heap)(implicit ctx: Context): Res = fun(valInfoFn, heap)
  }

  case class ObjectInfo(fun: (Symbol, Heap) => Res) extends LatentInfo {
    def select(sym: Symbol, heap: Heap)(implicit ctx: Context): Res = fun(sym, heap)
  }

  class Heap extends Cloneable {
    private var _parent: Heap = null
    protected var _envMap: Map[Int, Env] = Map()

    def apply(id: Int) =_envMap(id)

    def contains(id: Int) = _envMap.contains(id)

    def addEnv(env: Env) = {
      env.heap = this
      _envMap += env.id -> env
    }

    override def clone: Heap = {
      val heap = new Heap
      heap._parent = this

      this._envMap.foreach { case (id, env) =>
        val env2 = env.clone
        env2.heap = heap
        heap._envMap = heap._envMap.updated(id, env2)
      }

      heap
    }

    def join(heap2: Heap): Heap = {
      assert(heap2._parent `eq` this)
      heap2._envMap.foreach { case (id: Int, env: Env) =>
        if (this.contains(id))
          this._envMap = this._envMap.updated(id, this(id).join(env))
        else {
          env.heap = this
          this._envMap = this._envMap.updated(id, env)
        }
      }
      this
    }
  }

  object State {
    val Partial = 1
    val Filled  = 2
    val Full    = 3
  }

  case class ValueInfo(state: Int = State.Full, latentInfo: LatentInfo = NoLatent) {
    def isPartial = state == State.Partial
    def isFilled  = state == State.Filled
    def isFull    = state == State.Full
  }

  case class SymInfo(assigned: Boolean = false, forced: Boolean = false, state: Int = State.Full, latentInfo: LatentInfo = NoLatent) {
    def isPartial = assigned && state == State.Partial
    def isFilled  = assigned && state == State.Filled
    def isFull    = assigned && state == State.Full

    def isLatent  = latentInfo != NoLatent

    def setAssigned = this.copy(assigned = true)
  }

  object Env {
    private var uniqueId = 0
    def newId: Int = {
      uniqueId += 1
      uniqueId
    }
  }

  /** The state of method stack and objects
   *
   *  @param outerId required for modelling closures
   *
   *  Invariant: the data stored in the mutable map must be immutable
   */
  class Env(val outerId: Int) extends Cloneable {
    val id: Int = Env.uniqueId

    var heap: Heap = null

    protected var _syms: Map[Symbol, SymInfo] = Map()

    def outer: Env = heap(outerId)

    override def clone: Env = super.clone.asInstanceOf[Env]

    def deepClone: Env = {
      val heap2 = heap.clone
      heap2(this.id)
    }

    def newEnv(heap: Heap = this.heap): FreshEnv = {
      val env = new Env(outerId)
      heap.addEnv(env)
      env
    }

    def add(sym: Symbol, info: SymInfo) = _syms(sym) = info

    def info(sym: Symbol): Boolean =
      if (_syms.contains(sym)) _syms(sym)
      else outer.info(sym)

    def state: Int =
      if (_syms.contains(sym)) _syms(sym).state
      else outer.getState(sym)
    def setState(sym: Symbol, state: State): Unit =
      if (_syms.contains(sym)) _syms(sym) = _syms(sym).copy(state = state)
      else outer.setState(sym)

    def isLatent(sym: Symbol): Boolean =
      if (_syms.contains(sym)) _syms(sym).isLatent
      else outer.isLatent(sym)
    def setLatent(sym: Symbol, info: LatentInfo): Unit =
      if (_syms.contains(sym)) _syms(sym) = _syms(sym).copy(latentInfo = info)
      else outer.setLatent(sym, info)
    def latentInfo(sym: Symbol): LatentInfo =
      if (_syms.contains(sym)) _syms(sym).latentInfo
      else outer.latentInfo(sym)

    def isForced(sym: Symbol): Boolean =
      if (_syms.contains(sym)) _syms(sym).forced
      else outer.isForced(sym)
    def setForced(sym: Symbol): Unit =
      if (_syms.contains(sym)) _syms(sym) = _syms(sym).copy(forced = true)
      else outer.setForced(sym)

    def isAssigned(sym: Symbol): Boolean =
      if (_syms.contains(sym)) _syms(sym).assigned
      else outer.isAssigned(sym)
    def setAssigned(sym: Symbol): Unit =
      if (_syms.contains(sym)) _syms(sym) = _syms(sym).copy(assigned = true)
      else outer.setAssigned(sym)

    def notAssigned = _syms.keys.filter(sym => !_syms(sym).assigned)
    def partialSyms = _syms.keys.filter(sym => _syms(sym).isPartial)
    def filledSyms  = _syms.keys.filter(sym => _syms(sym).isFilled)
    def forcedSyms  = _syms.keys.filter(sym => _syms(sym).forced)
    def latentSyms  = _syms.keys.filter(sym => _syms(sym).isLatent)

    def join(env2: Env): Env = {
      assert(this.id == env2.id)

      _syms.foreach { case (sym: Symbol, info: SymInfo) =>
        assert(env2.contains(sym))
        val info2 = env2._syms(sym)
        if (!info.assigned || !info2.assigned)
          _syms(sym) = info.copy(assigned = false)
        else
          _syms(sym) = info.copy(
            assigned   =  false,
            forced     =  info.forced || info2.forced,
            state      =  Math.min(info.state, info2.state),
            latentInfo =  info.latentInfo.join(info2.latentInfo)
          )
      }

      this
    }

    override def toString: String =
      (if (outerId > 0) outer.toString + "\n" else "") ++
      s"""~ -------------------------------------
          ~ | locals:  ${_syms.keys}
          ~ | not initialized:  ${notAssigned}
          ~ | partial: ${partialSyms}
          ~ | filled: ${filledSyms}
          ~ | lazy forced:  ${forcedSyms}
          ~ | latent symbols: ${latentSyms}"""
      .stripMargin('~')
  }

  case class Res(var effects: Effects = Vector.empty, var state: Int = State.Full, var latentInfo: LatentInfo = NoLatent) {
    def isLatent  = latentInfo != NoLatent

    def isPartial = state == State.Partial
    def isFilled  = state == State.Filled
    def isFull    = state == State.Full

    def +=(eff: Effect): Unit = effects = effects :+ eff
    def ++=(effs: Effects) = effects ++= effs

    def force(valInfofn: Int => ValueInfo, heap: Heap)(implicit ctx: Context): Res = {
      latentInfo.asMethod.apply(valInfofn, heap)
    }

    def select(tree: tpd.Tree, sym: Symbol, heap: Heap)(implicit ctx: Context): Res = {
      if (isLatent) latentInfo.asObject.select(tree, sym, heap)
      else Res()
    }

    def join(res2: Res)(implicit ctx: Context): Res =
      if (!isLatent) {
        res2 ++= this.effects
        res2.state = Math.min(res2.state, this.state)
        res2
      }
      else if (!res2.isLatent) {
        this ++= res2.effects
        this.state = Math.min(res2.state, this.state)
        this
      }
      else Res(
        effects    = res2.effects ++ this.effects,
        partial    = res2.isPartial || this.isPartial,
        latentInfo = res2.latentInfo.join(latentInfo)
      )

    override def toString: String =
      s"""~Res(
          ~| effects = ${if (effects.isEmpty) "()" else effects.mkString("\n|    - ", "\n|    - ", "")}
          ~| partial = $isPartial
          ~| filled  = $isFilled
          ~| latent  = $latentInfo
          ~)"""
      .stripMargin('~')
  }

  // TODO: default methods are not necessarily safe, if they call other methods
  def isDefaultGetter(sym: Symbol)(implicit ctx: Context) = sym.name.is(NameKinds.DefaultGetterName)

  def hasPartialParam(cls: ClassSymbol)(implicit ctx: Context): Boolean =
    cls.paramAccessors.exists(_.hasAnnotation(defn.PartialAnnot))

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
}

class DataFlowChecker {

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

  def checkForce(sym: Symbol, pos: Position, env: Env)(implicit ctx: Context): Res =
    if (sym.is(Lazy) && !env.isForced(sym)) {
      env.addForced(sym)
      indentedDebug(s">>> forcing $sym")
      val res = env.latentInfo(sym).asMethod.apply(i => null, env.heap)

      if (res.isPartial) env.addPartial(sym)
      if (res.isLatent) env.addLatent(sym, res.latentInfo)

      if (res.effects.nonEmpty) res.copy(effects = Vector(Force(sym, res.effects, pos)))
      else res
    }
    else
      Res(
        partial = env.isPartial(sym),
        latentInfo = if (env.isLatent(sym)) env.latentInfo(sym) else null
      )

  def checkParams(sym: Symbol, paramInfos: List[Type], args: List[Tree], env: Env, force: Boolean)(implicit ctx: Context): (Res, Vector[ValueInfo]) = {
    def isParamPartial(index: Int) = paramInfos(index).dealiasKeepAnnots.hasAnnotation(defn.PartialAnnot)

    var effs = Vector.empty[Effect]
    var infos = Vector.empty[ValueInfo]
    var partial = false

    args.zipWithIndex.foreach { case (arg, index) =>
      val res = apply(arg, env)
      effs ++= res.effects
      partial = partial || res.isPartial
      infos = infos :+ ValueInfo(res.isPartial, res.latentInfo)

      if (res.isLatent && force) {
        val effs2 = res.force(i => ValueInfo(), env.heap)            // latent values are not partial
        if (effs2.effects.nonEmpty) {
          partial = true
          if (!isParamPartial(index)) effs = effs :+ Latent(arg, effs2.effects)
        }
      }
      if (res.isPartial && !isParamPartial(index) && force) effs = effs :+ Argument(sym, arg)
    }

    (Res(effects = effs, partial = partial), infos)
  }

  def checkNew(tree: Tree, tref: TypeRef, init: TermRef, argss: List[List[tpd.Tree]], env: Env)(implicit ctx: Context): Res = {
    val paramInfos = init.widen.paramInfoss.flatten
    val args = argss.flatten

    val (res1, _) = checkParams(tref.symbol, paramInfos, args, env, force = true)

    if (tref.symbol == env.currentClass) {
      res1 += RecCreate(tref.symbol, tree)
      return res1
    }

    if (!(localRef(tref, env).exists)) return res1

    if (!isLexicalRef(tref, env)) {
      if (isPartial(tref.prefix, env) && !isSafeVirtualAccess(tref, env))
        res1 += PartialNew(tref.prefix, tref.symbol, tree.pos)
      res1
    }
    else {
      indentedDebug(s">>> create new instance ${tref.symbol}")
      val latentInfo = env.latentInfo(tref.symbol).asMethod
      val res2 = latentInfo(i => null, env.heap)               // TODO: propagate params to init
      if (res2.effects.nonEmpty && !ctx.owner.is(Synthetic)) res2 += Instantiate(tref.symbol, res2.effects, tree.pos)
      res2
    }
  }

  def checkApply(tree: tpd.Tree, fun: Tree, argss: List[List[Tree]], env: Env)(implicit ctx: Context): Res = {
    val res1 = apply(fun, env)

    val args = argss.flatten
    val paramInfos = fun.tpe.widen.paramInfoss.flatten
    val (res2, valueInfos) = checkParams(fun.symbol, paramInfos, args, env, force = !res1.isLatent)

    var effs = res1.effects ++ res2.effects

    if (res1.isLatent) {
      indentedDebug(s">>> calling ${fun.symbol}")
      val res3 = res1.force(i => valueInfos(i), env.heap)
      if (res3.effects.nonEmpty) effs = effs :+ Latent(tree, res3.effects)

      res3.copy(effects = effs)
    }
    else Res(effects = effs)
  }

  def checkSelect(tree: Select, env: Env)(implicit ctx: Context): Res = {
    if (tree.qualifier.tpe.dealias <:< env.currentClass.thisType) {
      return checkTermRef(tree, env)
    }

    val res = apply(tree.qualifier, env)

    if (res.isPartial)
      res += Member(tree.symbol, tree.qualifier, tree.pos)

    if (res.isLatent && res.latentInfo.isObject) {
      val res2 = res.select(tree, tree.symbol, env.heap)
      res2 ++= res.effects
      res2
    }
    else res
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
    case NamedTypeEx(ThisType(tref), _) if tref.symbol.isContainedIn(env.currentClass) => tp
    case NamedTypeEx(SuperType(ThisType(tref), _), _) if tref.symbol.isContainedIn(env.currentClass) => tp
    case ref @ NamedTypeEx(NoPrefix, _) if ref.symbol.isContainedIn(env.currentClass) => ref
    case ref @ NamedTypeEx(tp: TermRef, _) =>
      if (tp <:< env.currentClass.thisType) ref    // tp is alias of `this`
      else localRef(tp, env)
    case _ => NoType
  }

  object NamedTypeEx {
    def unapply(tp: NamedType)(implicit ctx: Context): Option[(Type, Symbol)] = tp match {
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
  def isSafeVirtualAccess(tp: NamedType, env: Env)(implicit ctx: Context): Boolean =
    tp.symbol.owner.isClass &&
      (env.currentClass.isSubClass(tp.symbol.owner) ||
         env.currentClass.givenSelfType.classSymbols.exists(_.isSubClass(tp.symbol.owner))) &&
      (
        tp.symbol.isTerm && tp.symbol.is(AnyFlags, butNot = Method | Lazy | Deferred) && !hasPartialParam(env.currentClass) ||
        tp.symbol.hasAnnotation(defn.InitAnnot) || tp.symbol.hasAnnotation(defn.PartialAnnot) ||
        isDefaultGetter(tp.symbol) || (env.thisInitialized && env.currentClass.is(Final))
      )


  def isPartial(tp: Type, env: Env)(implicit ctx: Context): Boolean = tp match {
    case tmref: TermRef             => env.isPartial(tmref.symbol)
    case ThisType(tref)             => env.isPartial(tref.symbol)
    case SuperType(thistp, _)       => isPartial(thistp, env)        // super is partial if `thistp` is partial
    case _                          => false
  }

  def checkLexicalLocalRef(sym: Symbol, env: Env, pos: Position)(implicit ctx: Context): Res = {
    var effs = Vector.empty[Effect]

    if (env.isNotInit(sym)) effs = effs :+ Uninit(sym, pos)

    if (sym.is(Deferred) && !sym.hasAnnotation(defn.InitAnnot))
      effs = effs :+ UseAbstractDef(sym, pos)

    if (sym.is(Lazy)) {                // a forced lazy val could be partial and latent
      val res2 = checkForce(sym, pos, env)
      res2.copy(effects = effs ++ res2.effects)
    }
    else if (sym.is(Method)) {
      // TODO: check only on `this`
      // if (!(sym.hasAnnotation(defn.InitAnnot) || sym.isEffectivelyFinal || isDefaultGetter(sym)))
      //   effs = effs :+ OverrideRisk(sym, pos)

      if (sym.info.isInstanceOf[ExprType] && env.isLatent(sym)) {       // parameter-less call
        val latentInfo = env.latentInfo(sym).asMethod
        val res2 = latentInfo(i => null, env.heap)

        if (res2.effects.nonEmpty) res2.copy(effects = Vector(Call(sym, effs ++ res2.effects, pos)))
        else res2.copy(effects = effs)
      }
      else {
        val info = if (env.isLatent(sym)) env.latentInfo(sym) else null
        Res(effects = effs, latentInfo = info)
      }
    } else
      Res(
        effects = effs,
        partial = env.isPartial(sym),
        latentInfo = if (env.isLatent(sym)) env.latentInfo(sym) else null
      )
  }

  // precondition: `env` should be the owner environment of `tree.symbol`
  def checkTermRef(tree: Tree, env: Env)(implicit ctx: Context): Res = {
    indentedDebug(s"${tree.show} is local ? = " + localRef(tree.tpe, env).exists)

    val ref: TermRef = localRef(tree.tpe, env) match {
      case NoType         => return Res()
      case tmref: TermRef => tmref
    }

    val sym = ref.symbol

    if (isLexicalRef(ref, env)) checkLexicalLocalRef(sym, env, tree.pos)
    else {
      var effs = Vector.empty[Effect]
      if (isPartial(ref.prefix, env) && !isSafeVirtualAccess(ref, env))
        effs =  effs :+ Member(sym, tree, tree.pos)

      Res(
        effects = effs,
        partial = env.isPartial(sym),
        latentInfo = if (env.isLatent(sym)) env.latentInfo(sym) else null
      )
    }
  }

  def checkClosure(sym: Symbol, tree: Tree, env: Env)(implicit ctx: Context): Res = {
    Res(
      partial = false,
      latentInfo = env.latentInfo(sym)
    )
  }

  def checkIf(tree: If, env: Env)(implicit ctx: Context): Res = {
    val If(cond, thenp, elsep) = tree

    val res1: Res = apply(cond, env)

    val envClone = env.deepClone
    val res2: Res = apply(thenp, env)
    val res3: Res = apply(elsep, envClone)

    env.heap.join(envClone.heap)

    res2.copy(effects = res1.effects ++ res2.effects).join(res3)
  }

  def checkValDef(vdef: ValDef, env: Env)(implicit ctx: Context): Res = {
    val res1 = apply(vdef.rhs, env)

    if (!tpd.isWildcardArg(vdef.rhs) && !vdef.rhs.isEmpty)
      env.addInit(vdef.symbol)     // take `_` as uninitialized, otherwise it's initialized

    if (res1.isPartial && !env.thisInitialized) {
      env.addPartial(vdef.symbol)
    }

    if (res1.isLatent)
      env.addLatent(vdef.symbol, res1.latentInfo)

    Res(effects = res1.effects)
  }

  def checkStats(stats: List[Tree], env: Env)(implicit ctx: Context): Res =
    stats.foldLeft(Res()) { (acc, stat) =>
      indentedDebug(s"acc = ${pad(acc.toString)}")
      val res1 = apply(stat, env)
      acc.copy(effects = acc.effects ++ res1.effects)
    }

  def checkBlock(tree: Block, env: Env)(implicit ctx: Context): Res = {
    val env2 = env.heap.newEnv(env.id)
    indexStats(tree.stats, env2)

    val res1 = checkStats(tree.stats, env2)
    val res2 = apply(tree.expr, env2)

    res2.copy(effects = res1.effects ++ res2.effects)
  }

  // TODO: method call should compute fix point
  protected var _methChecking: Set[Symbol] = Set()
  def isChecking(sym: Symbol)   = _methChecking.contains(sym)
  def checking[T](sym: Symbol)(fn: => T) = {
    _methChecking += sym
    val res = fn
    _methChecking -= sym
    res
  }

  def indexClassDef(tdef: TypeDef, env: Env)(implicit ctx: Context): Unit = {
    def nonStaticStats = tdef.rhs.asInstanceOf[Template].body.filter {
      case vdef : ValDef  =>
        !vdef.symbol.hasAnnotation(defn.ScalaStaticAnnot)
      case stat =>
        true
    }

    val tmpl = tdef.rhs.asInstanceOf[Template]

    // TODO: handle params to init
    val latent = MethodInfo { (valInfoFn, heap) =>
      if (isChecking(tdef.symbol)) {
        debug(s"recursive creation of ${tdef.symbol} found during initialization of ${env.currentClass}")
        Res()
      }
      else checking(tdef.symbol) {
        val env2 = env.newEnv(heap)
        indexStats(nonStaticStats, env2)

        apply(tmpl, env2)(ctx.withOwner(tdef.symbol)).copy(latentInfo = new ObjectEnv(id = env2.id))
      }
    }
    env.addLocal(tdef.symbol)
    env.addLatent(tdef.symbol, latent)
  }

  def indexStats(stats: List[Tree], env: Env)(implicit ctx: Context): Unit = stats.foreach {
    case ddef: DefDef if ddef.symbol.is(AnyFlags, butNot = Accessor) =>
      val latenInfo = MethodInfo { (valInfoFn, heap) =>
        if (isChecking(ddef.symbol)) {
          debug(s"recursive call of ${ddef.symbol} found during initialization of ${env.currentClass}")
          Res()
        }
        else {
          val env2 = heap.newEnv(env.id)
          ddef.vparamss.flatten.zipWithIndex.foreach { case (param: ValDef, index: Int) =>
            val paramInfo = valInfoFn(index)
            env2.addLocal(param.symbol)
            if (paramInfo.isLatent) env2.addLatent(param.symbol, paramInfo.latentInfo)
            if (paramInfo.partial) env2.addPartial(param.symbol)
          }

          checking(ddef.symbol) { apply(ddef.rhs, env2)(ctx.withOwner(ddef.symbol)) }
        }
      }

      env.addLocal(ddef.symbol)
      env.addLatent(ddef.symbol, latenInfo)
    case vdef: ValDef if vdef.symbol.is(Lazy)  =>
      val latent = MethodInfo { (valInfoFn, heap) =>
        val env2 = heap(env.id)
        if (isChecking(vdef.symbol)) {
          debug(s"recursive forcing of lazy ${vdef.symbol} found during initialization of ${env.currentClass}")
          Res()
        }
        else checking(vdef.symbol) {
          apply(vdef.rhs, env2)
        }
      }
      env.addLocal(vdef.symbol)
      env.addLatent(vdef.symbol, latent)
    case tdef: TypeDef if tdef.isClassDef  =>
      indexClassDef(tdef, env)
    case mdef: MemberDef =>
      env.addLocal(mdef.symbol)
    case _ =>
  }

  def apply(tree: Tree, env: Env)(implicit ctx: Context): Res = trace("checking " + tree.show, env)(tree match {
    case tmpl: Template =>
      // TODO: check parents
      checkStats(tmpl.body, env)
    case vdef : ValDef if !vdef.symbol.is(Lazy) =>
      checkValDef(vdef, env)
    case _: DefTree =>  // ignore other definitions
      Res()
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
      if (env.currentClass == tree.symbol && !env.thisInitialized)
        Res(partial = true)
      else
        Res()
    case tree @ Super(qual, mix) =>
      if (env.isPartial(qual.symbol) && !env.thisInitialized) Res(partial = true)
      else Res()
    case tree @ If(cond, thenp, elsep) =>
      checkIf(tree, env)
    case tree @ Apply(_, _) =>
      val (fn, targs, vargss) = decomposeCall(tree)
      checkApply(tree, fn, vargss, env)
    case tree @ Assign(lhs @ (Ident(_) | Select(This(_), _)), rhs) =>
      val resRhs = apply(rhs, env)

      if (!resRhs.isPartial || env.isPartial(lhs.symbol) || env.isNotInit(lhs.symbol)) {
        if (env.isNotInit(lhs.symbol)) env.addInit(lhs.symbol)
        if (!resRhs.isPartial) env.removePartial(lhs.symbol)
        else env.addPartial(lhs.symbol)
      }
      else resRhs += CrossAssign(lhs, rhs)

      resRhs.copy(partial = false, latentInfo = null)
    case tree @ Assign(lhs @ Select(prefix, _), rhs) =>
      val resLhs = apply(prefix, env)
      val resRhs = apply(rhs, env)

      val res = Res(effects = resLhs.effects ++ resRhs.effects)

      if (resRhs.isPartial && !resLhs.isPartial)
        res += CrossAssign(lhs, rhs)

      res
    case tree @ Block(stats, expr) =>
      checkBlock(tree, env)
    case Typed(expr, tpd) =>
      apply(expr, env)
    case _ =>
      Res()
  })
}