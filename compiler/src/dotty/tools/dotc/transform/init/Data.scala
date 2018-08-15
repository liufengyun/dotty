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
    case RecCreate(cls, tree) =>
      ctx.warning(s"Possible recursive creation of instance for ${cls.show}", tree.pos)
    case Generic(msg, pos) =>
      ctx.warning(msg, pos)

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
case class Generic(msg: => String, pos: Position) extends Effect                     // generic problem

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

  def join(other: LatentInfo): LatentInfo = (this, other) match {
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
      ObjectInfo {
        (sym: Symbol, heap: Heap) => {
          val res1 = o1.select(sym, heap)
          val res2 = o2.select(sym, heap)
          res1.join(res2)
        }
      }
    case _ =>
      throw new Exception(s"Can't join $this and $other")
  }
}

object NoLatent extends LatenInfo

case class MethodInfo(fun: (Int => ValueInfo, Heap) => Res) extends LatentInfo {
  def apply(valInfoFn: Int => ValueInfo, heap: Heap): Res = fun(valInfoFn, heap)
}

case class ObjectInfo(fun: (Symbol, Heap, Position) => Res) extends LatentInfo {
  def select(sym: Symbol, heap: Heap, pos: Position): Res = fun(sym, heap, pos)
}

//=======================================
//           Heap / Env
//=======================================

class Heap extends Cloneable {
  private var _parent: Heap = null
  protected var _envMap: mutable.Map[Int, Env] = Map()

  def apply(id: Int) =_envMap(id)

  def contains(id: Int) = _envMap.contains(id)

  def addEnv(env: Env) = {
    env.heap = this
    _envMap(env.id) = env
  }

  override def clone: Heap = {
    val heap = new Heap
    heap._parent = this

    this._envMap.foreach { case (id, env) =>
      val env2 = env.clone
      env2.heap = heap
      heap(id) = env2
    }

    heap
  }

  def join(heap2: Heap): Heap = {
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

class State(state: Int) extends AnyVal {
  def join(other: State): State = new State(Math.min(state, other.state))
}

object State {
  val Partial = new State(1)
  val Filled  = new State(2)
  val Full    = new State(3)
}

case class ValueInfo(state: State = State.Full, latentInfo: LatentInfo = NoLatent) {
  def isPartial = state == State.Partial
  def isFilled  = state == State.Filled
  def isFull    = state == State.Full
}

case class SymInfo(assigned: Boolean = false, forced: Boolean = false, state: State = State.Full, latentInfo: LatentInfo = NoLatent) {
  def isPartial = assigned && state == State.Partial
  def isFilled  = assigned && state == State.Filled
  def isFull    = assigned && state == State.Full

  def isLatent  = latentInfo != NoLatent
}

object Env {
  private var uniqueId = 0
  def newId: Int = {
    uniqueId += 1
    uniqueId
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

  def update(sym: Symbol, info: SymInfo) = _syms(sym) = info

  def apply(sym: Symbol): SymInfo =
    if (_syms.contains(sym)) _syms(sym)
    else outer.info(sym)

  def state: State =
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
      // path-insensitive approximation:
      // 1. if a variable is assigned in one branch, but not in the other branch, we
      //    treat the variable as not assigned.
      // 2. a lazy variable is force if it's forced in either branch
      // 3. a variable gets the lowest possible state
      if (!info.assigned || !info2.assigned)
        _syms(sym) = info.copy(assigned = false, latentInfo == NoLatent)
      else
        _syms(sym) = info.copy(
          assigned   =  false,
          forced     =  info.forced || info2.forced,
          state      =  info.state.join(info2.state),
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

  def call(valInfofn: Int => ValueInfo, heap: Heap)(implicit ctx: Context): Res = {
    latentInfo.asMethod.apply(valInfofn, heap)
  }

  def select(tree: tpd.Tree, sym: Symbol, heap: Heap)(implicit ctx: Context): Res = {
    if (isLatent) latentInfo.asObject.select(tree, sym, heap)
    else Res()
  }

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

  override def toString: String =
    s"""~Res(
        ~| effects = ${if (effects.isEmpty) "()" else effects.mkString("\n|    - ", "\n|    - ", "")}
        ~| partial = $isPartial
        ~| filled  = $isFilled
        ~| latent  = $latentInfo
        ~)"""
    .stripMargin('~')
}
