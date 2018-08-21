package dotty.tools.dotc
package transform
package init

import core._
import Contexts.Context
import StdNames._
import Names._
import ast._
import Trees._
import Symbols._
import Types._
import Decorators._
import util.Positions._
import config.Printers.init.{ println => debug }
import collection.mutable

//=======================================
//             Effects
//=======================================

sealed trait Effect {
  def report(implicit ctx: Context): Unit = this match {
    case Uninit(sym, pos)         =>
      ctx.warning(s"Reference to uninitialized value `${sym.name}`", pos)
    case OverrideRisk(sym, pos)     =>
      ctx.warning(s"`@partial` or `@filled` is recommended for $sym for safe overriding", sym.pos)
      ctx.warning(s"Reference to $sym which could be overriden", pos)
    case Call(sym, effects, pos)  =>
      ctx.warning(s"The call to `${sym.name}` causes initialization problem", pos)
      effects.foreach(_.report)
    case Force(sym, effects, pos) =>
      ctx.warning(s"Forcing lazy val `${sym.name}` causes initialization problem", pos)
      effects.foreach(_.report)
    case Instantiate(cls, effs, pos)  =>
      ctx.warning(s"Create instance results in initialization errors", pos)
      effs.foreach(_.report)
    case UseAbstractDef(sym, pos)  =>
      ctx.warning(s"`@scala.annotation.init` is recommended for abstract $sym for safe initialization", sym.pos)
      ctx.warning(s"Reference to abstract $sym which should be annotated with `@scala.annotation.init`", pos)
    case Latent(tree, effs)  =>
      ctx.warning(s"Latent effects results in initialization errors", tree.pos)
      effs.foreach(_.report)
    case Generic(msg, pos) =>
      ctx.warning(msg, pos)

  }
}

case class Uninit(sym: Symbol, pos: Position) extends Effect                         // usage of uninitialized values
case class OverrideRisk(sym: Symbol, pos: Position) extends Effect                   // calling methods that are not override-free
case class Call(sym: Symbol, effects: Seq[Effect], pos: Position) extends Effect     // calling method results in error
case class Force(sym: Symbol, effects: Seq[Effect], pos: Position) extends Effect    // force lazy val results in error
case class Instantiate(cls: Symbol, effs: Seq[Effect], pos: Position) extends Effect // create new instance of in-scope inner class results in error
case class UseAbstractDef(sym: Symbol, pos: Position) extends Effect                 // use abstract def during initialization, see override5.scala
case class Latent(tree: tpd.Tree, effs: Seq[Effect]) extends Effect                  // problematic latent effects (e.g. effects of closures)
case class Generic(msg: String, pos: Position) extends Effect                     // generic problem

object Effect {
  type Effects = Vector[Effect]
}

//=======================================
//               LatentInfo
//=======================================

sealed trait LatentInfo {
  def asMethod: MethodInfo = this.asInstanceOf[MethodInfo]
  def asObject: ObjectInfo = this.asInstanceOf[ObjectInfo]
  def isMethod: Boolean = this.isInstanceOf[MethodInfo]
  def isObject: Boolean = !isMethod

  def join(other: LatentInfo)(implicit ctx: Context): LatentInfo = (this, other) match {
    case (NoLatent, _) => other
    case (_, NoLatent) => this
    case (m1: MethodInfo, m2: MethodInfo) =>
      MethodInfo {
        (fn: Int => ValueInfo, heap: Heap) => {
          val res1 = m1.apply(fn, heap)
          val res2 = m2.apply(fn, heap)
          res1.join(res2)
        }
      }
    case (o1: ObjectInfo, o2: ObjectInfo) =>
      ObjectInfo(
        (sym: Symbol, heap: Heap, pos: Position) => {
          val res1 = o1.select(sym, heap, pos)
          val res2 = o2.select(sym, heap, pos)
          res1.join(res2)
        },
        (sym: Symbol, valInfo: ValueInfo, heap: Heap, pos: Position) => {
          o1.assign(sym, valInfo, heap, pos)
          o2.assign(sym, valInfo, heap, pos)
        }
      )
    case _ =>
      throw new Exception(s"Can't join $this and $other")
  }
}

object NoLatent extends LatentInfo

case class MethodInfo(fun: (Int => ValueInfo, Heap) => Res) extends LatentInfo {
  def apply(valInfoFn: Int => ValueInfo, heap: Heap): Res = fun(valInfoFn, heap)
}

case class ObjectInfo(
  select: (Symbol, Heap, Position) => Res,
  assign: (Symbol, ValueInfo, Heap, Position) => Res) extends LatentInfo

//=======================================
//           Heap / Env
//=======================================

class Heap extends Cloneable {
  private var _parent: Heap = null
  protected var _envMap: mutable.Map[Int, Env] = mutable.Map()

  def apply(id: Int) =_envMap(id)

  def contains(id: Int) = _envMap.contains(id)

  def addEnv(env: Env) = {
    env.heap = this
    _envMap(env.id) = env
  }

  override def clone: Heap = {
    val heap = new Heap
    heap._parent = this
    heap._envMap = mutable.Map()

    this._envMap.foreach { case (id, env) =>
      val env2 = env.clone
      env2.heap = heap
      heap._envMap(id) = env2
    }

    heap
  }

  def join(heap2: Heap)(implicit ctx: Context): Heap = {
    assert(heap2._parent `eq` this)
    heap2._envMap.foreach { case (id: Int, env: Env) =>
      if (this.contains(id))
        this._envMap(id) = this(id).join(env)
      else {
        env.heap = this
        this._envMap(id) = env
      }
    }
    this
  }
}

class State(val state: Int) extends AnyVal {
  def isPartial = this == State.Partial
  def isFilled  = this == State.Filled
  def isFull    = this == State.Full

  def join(other: State): State = new State(Math.min(state, other.state))

  def <(other: State): Boolean = this.state < other.state
}

object State {
  val Partial = new State(1)
  val Filled  = new State(2)
  val Full    = new State(3)

  def max(s1: State, s2: State): State = new State(Math.max(s1.state, s2.state))
}

case class ValueInfo(state: State = State.Full, latentInfo: LatentInfo = NoLatent) {
  def isPartial = state.isPartial
  def isFilled  = state.isFilled
  def isFull    = state.isFull

  def isLatent  = latentInfo != NoLatent
}

case class SymInfo(assigned: Boolean = true, forced: Boolean = false, state: State = State.Full, latentInfo: LatentInfo = NoLatent) {
  def isPartial = assigned && state.isPartial
  def isFilled  = assigned && state.isFilled
  def isFull    = assigned && state.isFull

  def isLatent  = latentInfo != NoLatent
}

object Env {
  private[this] var _uniqueId = 0
  def uniqueId: Int = {
    _uniqueId += 1
    _uniqueId
  }

  class RootEnv extends Env(-1) {
    override def contains(sym: Symbol): Boolean = _syms.contains(sym)
  }

  def createRootEnv: Env = {
    val heap = new Heap
    val env = new RootEnv
    heap.addEnv(env)
    env
  }
}

/** The state of closure and objects
  *
  *  @param outerId required for modelling closures
  *
  *  Invariants:
  *  1. the data stored in the immutable map must be immutable
  *  2. environment refer each other via `id`, which implies LatentInfo should
  *     never use captured environment other than its `id`.
  */
class Env(outerId: Int) extends Cloneable {
  val id: Int = Env.uniqueId

  assert(outerId != id)

  var heap: Heap = null

  protected var _syms: Map[Symbol, SymInfo] = Map()

  def outer: Env = heap(outerId)

  override def clone: Env = super.clone.asInstanceOf[Env]

  def deepClone: Env = {
    val heap2 = heap.clone
    heap2(this.id)
  }

  def nonObjectEnv: Env =
    if (this.isInstanceOf[ObjectEnv]) this.outer.nonObjectEnv
    else this

  def newEnv(heap: Heap = this.heap): Env = {
    val env = new Env(nonObjectEnv.id)
    heap.addEnv(env)
    env
  }

  def newObject(cls: ClassSymbol, heap: Heap = this.heap): ObjectEnv = {
    val env = new ObjectEnv(nonObjectEnv.id, cls)
    heap.addEnv(env)
    env
  }

  def add(sym: Symbol, info: SymInfo) =
    _syms = _syms.updated(sym, info)

  def update(sym: Symbol, info: SymInfo): Unit =
    if (_syms.contains(sym)) _syms = _syms.updated(sym, info)
    else outer.update(sym, info)

  def contains(sym: Symbol): Boolean = _syms.contains(sym) || outer.contains(sym)

  def apply(sym: Symbol): SymInfo = {
    if (_syms.contains(sym)) _syms(sym)
    else outer(sym)
  }

  def isAssigned(sym: Symbol): Boolean =
    if (_syms.contains(sym)) _syms(sym).assigned
    else outer.isAssigned(sym)
  def setAssigned(sym: Symbol): Unit =
    if (_syms.contains(sym)) _syms = _syms.updated(sym, _syms(sym).copy(assigned = true))
    else outer.setAssigned(sym)

  def notAssigned = _syms.keys.filter(sym => !(_syms(sym).assigned))
  def partialSyms = _syms.keys.filter(sym => _syms(sym).isPartial)
  def filledSyms  = _syms.keys.filter(sym => _syms(sym).isFilled)
  def forcedSyms  = _syms.keys.filter(sym => _syms(sym).forced)
  def latentSyms  = _syms.keys.filter(sym => _syms(sym).isLatent)

  def join(env2: Env)(implicit ctx: Context): Env = {
    assert(this.id == env2.id)

    _syms.foreach { case (sym: Symbol, info: SymInfo) =>
      assert(env2.contains(sym))
      val info2 = env2._syms(sym)
      // path-insensitive approximation:
      // 1. if a variable is assigned in one branch, but not in the other branch, we
      //    treat the variable as not assigned.
      // 2. a lazy variable is force if it's forced in either branch
      // 3. a variable gets the lowest possible state
      if (!info.assigned || !info2.assigned)
        _syms = _syms.updated(sym, info.copy(assigned = false, latentInfo = NoLatent))
      else
        _syms = _syms.updated(
          sym,
          info.copy(
            assigned   =  true,
            forced     =  info.forced || info2.forced,
            state      =  info.state.join(info2.state),
            latentInfo =  info.latentInfo.join(info2.latentInfo)
          )
        )
    }

    this
  }

  override def toString: String =
    (if (outerId > 0) outer.toString + "\n" else "") ++
    s"""~ --------------${getClass} - $id($outerId)-----------------------
        ~ | locals:  ${_syms.keys}
        ~ | not initialized:  ${notAssigned}
        ~ | partial: ${partialSyms}
        ~ | filled: ${filledSyms}
        ~ | lazy forced:  ${forcedSyms}
        ~ | latent symbols: ${latentSyms}"""
    .stripMargin('~')
}

class ObjectEnv(outerId: Int, val cls: ClassSymbol) extends Env(outerId) {
  // TODO: object environment should not resolve outer, only method environment resolves outer
  override def update(sym: Symbol, info: SymInfo): Unit = {
    assert(_syms.contains(sym))
    _syms = _syms.updated(sym, info)
  }

  override def contains(sym: Symbol): Boolean =
    _syms.contains(sym)

  override def apply(sym: Symbol): SymInfo =
    _syms(sym)

  override def isAssigned(sym: Symbol): Boolean =
    _syms(sym).assigned
  override def setAssigned(sym: Symbol): Unit =
    _syms = _syms.updated(sym, _syms(sym).copy(assigned = true))

  override def toString: String = super.toString ++ s"\n | class: $cls"
}

//=======================================
//           Res
//=======================================
import Effect._

case class Res(var effects: Effects = Vector.empty, var state: State = State.Full, var latentInfo: LatentInfo = NoLatent) {
  def isLatent  = latentInfo != NoLatent

  def isPartial = state == State.Partial
  def isFilled  = state == State.Filled
  def isFull    = state == State.Full

  def +=(eff: Effect): Unit = effects = effects :+ eff
  def ++=(effs: Effects) = effects ++= effs

  def hasErrors  = effects.size > 0

  def join(res2: Res)(implicit ctx: Context): Res =
    if (!isLatent) {
      res2 ++= this.effects
      res2.state = res2.state.join(this.state)
      res2
    }
    else if (!res2.isLatent) {
      this ++= res2.effects
      this.state = res2.state.join(this.state)
      this
    }
    else Res(
      effects    = res2.effects ++ this.effects,
      state      = res2.state.join(this.state),
      latentInfo = res2.latentInfo.join(latentInfo)
    )

  def valueInfo: ValueInfo = ValueInfo(state = state, latentInfo = latentInfo)

  override def toString: String =
    s"""~Res(
        ~| effects = ${if (effects.isEmpty) "()" else effects.mkString("\n|    - ", "\n|    - ", "")}
        ~| partial = $isPartial
        ~| filled  = $isFilled
        ~| latent  = $latentInfo
        ~)"""
    .stripMargin('~')
}
