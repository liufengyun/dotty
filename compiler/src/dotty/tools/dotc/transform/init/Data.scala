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
//           Heap / Env
//=======================================

trait HeapEntry extends Cloneable {
  val id: Int = Heap.uniqueId
  var heap: Heap = null

  override def clone: HeapEntry = super.clone.asInstanceOf[HeapEntry]
}

object Heap {
  private var _uniqueId = 0
  def uniqueId: Int = {
    _uniqueId += 1
    _uniqueId
  }

  class RootEnv extends Env(-1) {
    override def contains(sym: Symbol): Boolean = _syms.contains(sym)

    override def hasTree(sym: Symbol): Boolean = _symtab.contains(sym)

  }

  def createRootEnv: Env = {
    val heap = new Heap
    val env = new RootEnv
    heap.add(env)
    env
  }

  def join(entry1: HeapEntry, entry2: HeapEntry): HeapEntry = (entry1, entry2) match {
    case (env1: Env, env2: Env) =>
      env1.join(env2)
    case (obj1: ObjectRep, obj2: ObjectRep) =>
      obj1.join(obj2)
    case _ =>
      throw new Exception(s"Cannot join $entry1 and $entry2")
  }
}

class Heap extends Cloneable {
  private var _parent: Heap = null
  protected var _entries: mutable.Map[Int, HeapEntry] = mutable.Map()

  def apply(id: Int) =_entries(id)

  def contains(id: Int) = _entries.contains(id)

  def add(entry: HeapEntry) = {
    entry.heap = this
    _entries(entry.id) = entry
  }

  override def clone: Heap = {
    val heap = new Heap
    heap._parent = this
    heap._entries = mutable.Map()

    this._entries.foreach { case (id, entry) =>
      val entry2: HeapEntry = entry.clone
      entry2.heap = heap
      heap._entries(id) = entry2
    }

    heap
  }

  def join(heap2: Heap)(implicit ctx: Context): Heap = {
    assert(heap2._parent `eq` this)
    heap2._entries.foreach { case (id: Int, entry: HeapEntry) =>
      if (this.contains(id))
        this._entries(id) = Heap.join(this(id), entry)
      else {
        entry.heap = this
        this._entries(id) = entry
      }
    }
    this
  }
}

//=======================================
//           latent values
//=======================================

sealed trait LatentValue {
  def asFunction: FunctionValue = this.asInstanceOf[FunctionValue]
  def asObject: ObjectValue = this.asInstanceOf[ObjectValue]
  def isFunction: Boolean = this.isInstanceOf[FunctionValue]
  def isObject: Boolean = !isFunction

  def exists: Boolean = true

  def join(other: LatentValue): LatentValue = (this, other) match {
    case (NoLatent, _) => other
    case (_, NoLatent) => this
    case (m1: FunctionValue, m2: FunctionValue) =>
      FunctionValue {
        (fn: Int => ValueInfo, heap: Heap) => {
          val res1 = m1.apply(fn, heap)
          val res2 = m2.apply(fn, heap)
          res1.join(res2)
        }
      }
    case (o1: ObjectValue, o2: ObjectValue) =>
      ObjectValue(
        (sym: Symbol, heap: Heap, pos: Position) => {
          val res1 = o1.select(sym, heap, pos)
          val res2 = o2.select(sym, heap, pos)
          res1.join(res2)
        },
        (sym: Symbol, valInfo: ValueInfo, heap: Heap, pos: Position) => {
          o1.assign(sym, valInfo, heap, pos)
          o2.assign(sym, valInfo, heap, pos)
        },
        (sym: Symbol, valueInfos: List[ValueInfo], heap: Heap, objOpt: ObjectRep, pos: Position) => {
          val res1 = o1.init(sym, valueInfos, heap, objOpt, pos)
          val res2 = o2.init(sym, valueInfos, heap, objOpt, pos)
          res1.join(res2)
        }
      )
    case _ =>
      throw new Exception(s"Can't join $this and $other")
  }
}

object NoLatent extends LatentValue {
  override def exists: Boolean = false
}

case class FunctionValue(apply: (Int => ValueInfo, Heap) => Res) extends LatentValue

case class ObjectValue(
  select: (Symbol, Heap, Position) => Res,
  assign: (Symbol, ValueInfo, Heap, Position) => Res,
  init: (Symbol, List[ValueInfo], Heap, ObjectRep, Position) => Res) extends LatentValue

class State(val state: Int) {
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

case class ValueInfo(state: State = State.Full, latentValue: LatentValue = NoLatent) {
  def isPartial = state.isPartial
  def isFilled  = state.isFilled
  def isFull    = state.isFull

  def isLatent  = latentValue.exists
}

case class SymInfo(assigned: Boolean = true, forced: Boolean = false, state: State = State.Full, latentValue: LatentValue = NoLatent) {
  def isPartial = assigned && state.isPartial
  def isFilled  = assigned && state.isFilled
  def isFull    = assigned && state.isFull

  def isLatent  = latentValue.exists
}

//=======================================
//           environment
//=======================================

/** The state of closure and objects
  *
  *  @param outerId required for modelling closures
  *
  *  Invariants:
  *  1. the data stored in the immutable map must be immutable
  *  2. environment refer each other via `id`, which implies LatentValue should
  *     never use captured environment other than its `id`.
  */
class Env(outerId: Int) extends HeapEntry {
  assert(outerId != id)

  /** local symbols defined in current scope */
  protected var _syms: Map[Symbol, SymInfo] = Map()

  /** definitions introduced in current scope, class methods are in table for better performance */
  private var _symtab: mutable.Map[Symbol, Tree] = mutable.Map()
  def addTree(sym: Symbol, tree: Tree) = _symtab(sym) = tree
  def getTree[T <: Tree](sym: Symbol): (T, Int) =
    if (_symtab.contains(sym)) (_symtab(sym).asInstanceOf[T], id)
    else outer.getDef(sym)
  def hasTree(sym: Symbol): Boolean =
    _symtab.contains(sym) || super.hasTree(sym)

  def outer: Env = heap(outerId).asInstanceOf[Env]

  def deepClone: Env = {
    val heap2 = heap.clone
    heap2(this.id).asInstanceOf[Env]
  }

  def fresh(heap: Heap = this.heap): Env = {
    val env = new Env(this.id)
    heap.add(env)
    env
  }

  def apply(sym: Symbol): SymInfo =
    if (_syms.contains(sym)) _syms(sym)
    else outer(sym)

  def add(sym: Symbol, info: SymInfo) =
    _syms = _syms.updated(sym, info)

  def update(sym: Symbol, info: SymInfo): Unit =
    if (_syms.contains(sym)) _syms = _syms.updated(sym, info)
    else outer.update(sym, info)

  def contains(sym: Symbol): Boolean = _syms.contains(sym) || outer.contains(sym)

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
        _syms = _syms.updated(sym, info.copy(assigned = false, latentValue = NoLatent))
      else {
        val infoRes = info.copy(
          assigned   =  true,
          forced     =  info.forced || info2.forced,
          state      =  info.state.join(info2.state),
          latentValue =  info.latentValue.join(info2.latentValue)
        )
        _syms = _syms.updated(sym, infoRes)
      }
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


/** A container holds all information about fields and outers of an object
 */
class ObjectRep(envId: Int, val tp: Type) extends HeapEntry with Cloneable {
  override def clone: ObjectRep = super.clone.asInstanceOf[ObjectRep]

  def classSymbol(implicit ctx: Context): ClassSymbol = tp.classSymbol.asClass

  def env: Env = heap(envId).asInstanceOf[Env]

  protected var _fields: Map[Name, SymInfo] = Map()

  def apply(name: Name): SymInfo =
    _fields(name)

  def add(name: Name, info: SymInfo) =
    _fields = _fields.updated(name, info)

  // object environment should not resolve outer
  def update(name: Name, info: SymInfo): Unit = {
    assert(_fields.contains(name))
    _fields = _fields.updated(name, info)
  }

  def contains(name: Name): Boolean =
    _fields.contains(name)

  def isAssigned(name: Name): Boolean =
    _fields(name).assigned

  def setAssigned(name: Name): Unit =
    _fields = _fields.updated(name, _fields(name).copy(assigned = true))

  def notAssigned = _fields.keys.filter(name => !(_fields(name).assigned))
  def partialSyms = _fields.keys.filter(name => _fields(name).isPartial)
  def filledSyms  = _fields.keys.filter(name => _fields(name).isFilled)
  def forcedSyms  = _fields.keys.filter(name => _fields(name).forced)
  def latentSyms  = _fields.keys.filter(name => _fields(name).isLatent)

  def join(obj2: ObjectRep): ObjectRep = {
    assert(this.id == obj2.id)

    _fields.foreach { case (name: Name, info: SymInfo) =>
      assert(obj2.contains(name))
      val info2 = obj2._fields(name)
      // path-insensitive approximation:
      // 1. if a variable is assigned in one branch, but not in the other branch, we
      //    treat the variable as not assigned.
      // 2. a lazy variable is force if it's forced in either branch
      // 3. a variable gets the lowest possible state
      if (!info.assigned || !info2.assigned)
        _fields = _fields.updated(name, info.copy(assigned = false, latentValue = NoLatent))
      else {
        val infoRes = info.copy(
          assigned   =  true,
          forced     =  info.forced || info2.forced,
          state      =  info.state.join(info2.state),
          latentValue =  info.latentValue.join(info2.latentValue)
        )

        _fields = _fields.updated(name, infoRes)
      }
    }

    this
  }

  override def toString: String =
    s"""~ --------------${getClass} - $id($envId)-----------------------
        ~ | fields:  ${_fields.keys}
        ~ | not initialized:  ${notAssigned}
        ~ | partial: ${partialSyms}
        ~ | filled: ${filledSyms}
        ~ | lazy forced:  ${forcedSyms}
        ~ | latent symbols: ${latentSyms}
        ~ | class: $tp"""
    .stripMargin('~')
}

//=======================================
//           Res
//=======================================
import Effect._

case class Res(var effects: Effects = Vector.empty, var state: State = State.Full, var latentValue: LatentValue = NoLatent) {
  def isLatent  = latentValue != NoLatent

  def isPartial = state == State.Partial
  def isFilled  = state == State.Filled
  def isFull    = state == State.Full

  def +=(eff: Effect): Unit = effects = effects :+ eff
  def ++=(effs: Effects) = effects ++= effs

  def hasErrors  = effects.size > 0

  def join(res2: Res): Res =
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
      latentValue = res2.latentValue.join(latentValue)
    )

  def valueInfo: ValueInfo = ValueInfo(state = state, latentValue = latentValue)

  override def toString: String =
    s"""~Res(
        ~| effects = ${if (effects.isEmpty) "()" else effects.mkString("\n|    - ", "\n|    - ", "")}
        ~| partial = $isPartial
        ~| filled  = $isFilled
        ~| latent  = $latentValue
        ~)"""
    .stripMargin('~')
}


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
