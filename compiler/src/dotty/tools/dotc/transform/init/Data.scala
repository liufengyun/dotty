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
//             values
//=======================================

/** Abstract values in analysis */
sealed trait Value {
  /** Apply a method or function to the provided arguments */
  def apply(params: List[Value], heap: Heap): Res

  /** Select a member on a value */
  def select(sym: Symbol, heap: Heap, pos: Position): Res

  /** Assign on a value */
  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position): Res

  /** Index an inner class with current value as the immediate outer */
  def index(cls: ClassSymbol, tp: Type, obj: ObjectRep): Value

  /** Execute the constructor of an inner class for the fresh object `obj` */
  def init(sym: ClassSymbol, constr: Symbol, valueInfos: List[Value], heap: Heap, obj: ObjectRep, pos: Position): Res

  def join(other: Value): Value = (this, other) match {
    case (m1: FunctionValue, m2: FunctionValue) =>
      FunctionValue {
        (fn: Int => ValueInfo, heap: Heap) => {
          val res1 = m1.apply(fn, heap)
          val res2 = m2.apply(fn, heap)
          res1.join(res2)
        }
      }
    case (o1: AtomObjectValue, o2: AtomObjectValue) =>
      if (o1.id == o2.id) o1
      else new UnionObjectValue(Set(o1, o2))
    case (o1: UnionObjectValue, o2: UnionObjectValue) =>
      new UnionObjectValue(o1.values ++ o2.values)
    case (o1: UnionObjectValue, o2: AtomObjectValue) =>
      new UnionObjectValue(o1.values + o2)
    case (o1: AtomObjectValue, o2: UnionObjectValue) =>
      new UnionObjectValue(o2.values + o1)
    case _ =>
      throw new Exception(s"Can't join $this and $other")
  }
}

trait SingleValue extends Value

/** Union of values */
class UnionValue(val values: List[SingleValue]) extends Value {
  def apply(params: List[Value], heap: Heap): Res = {
    values.foldLeft(Res()) { (acc, value) =>
      value.apply(sym, heap, pos).join(acc)
    }
  }

  def select(sym: Symbol, heap: Heap, pos: Position): Res = {
    values.foldLeft(Res()) { (acc, value) =>
      value.select(sym, heap, pos).join(acc)
    }
  }

  def assign(sym: Symbol, valInfo: ValueInfo, heap: Heap, pos: Position): Res = {
    values.foldLeft(Res()) { (acc, value) =>
      value.assign(sym, valInfo, heap, pos).join(acc)
    }
  }

  def index(cls: ClassSymbol, tp: Type, obj: ObjectRep): ObjectValue = {
    val head :: tail = values.toList
    val value = head.index(cls, tp, obj)
    tail.foldLeft(value) { (acc, value) =>
      val obj2 = obj.fresh
      value.index(cls, tp, obj2).join(acc)
    }
  }

  def init(sym: ClassSymbol, constr: Symbol, valueInfos: List[ValueInfo], heap: Heap, obj: ObjectRep, pos: Position): Res = {
    val head :: tail = values.toList
    val res = head.init(sym, valueInfos, heap, obj, pos)
    tail.foldLeft(Res()) { (acc, value) =>
      val obj2 = obj.fresh
      value.init(sym, constr, valueInfos, heap, obj2, pos).join(acc)
    }
  }
}

/** Values that are subject to type checking rather than analysis */
class OpaqueValue(val state: Int) extends SingleValue {
  def isPartial = this == OpaqueValue.Partial
  def isFilled  = this == OpaqueValue.Filled
  def isFull    = this == OpaqueValue.Full

  def join(other: OpaqueValue): OpaqueValue = new OpaqueValue(Math.min(state, other.state))

  def <(other: OpaqueValue): Boolean = this.state < other.state
}

object OpaqueValue {
  val Partial = new OpaqueValue(1)
  val Filled  = new OpaqueValue(2)
  val Full    = new OpaqueValue(3)

  def max(s1: OpaqueValue, s2: OpaqueValue): OpaqueValue =
    new OpaqueValue(Math.max(s1.state, s2.state))
}

/** Values that are subject to analysis rather than type checking */
sealed trait TransparentValue extends SingleValue

/** A function value or value of method select */
case class FunctionValue(fun: (List[Value], Heap) => Res) extends TransparentValue {
  def apply(params: List[Value], heap: Heap): Res = fun(params, heap)

  def select(sym: Symbol, heap: Heap, pos: Position): Res = {
    assert(sym.name.toString == "apply")
    Res(value = this)
  }

  /** not supported */
  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position): Res = ???
  def index(cls: ClassSymbol, tp: Type, obj: ObjectRep): Value = ???
  def init(sym: ClassSymbol, constr: Symbol, valueInfos: List[Value], heap: Heap, obj: ObjectRep, pos: Position): Res = ???
}

/** An object value */
class ObjectValue(val id: Int)(implicit ctx: Context) extends TransparentValue {
  /** not supported, impossible to apply an object value */
  def apply(params: List[Value], heap: Heap): Res = ???

  def select(sym: Symbol, heap: Heap, pos: Position): Res = {
    val obj = heap(id).asInstanceOf[ObjectRep]
    Rules.select(obj, sym, pos)
  }

  def assign(sym: Symbol, valInfo: ValueInfo, heap: Heap, pos: Position): Res = {
    val obj = heap(id).asInstanceOf[ObjectRep]
    Rules.assign(obj, sym, valInfo, pos)
  }

  def index(cls: ClassSymbol, tp: Type, obj: ObjectRep): ObjectValue = {
    Indexing.indexInnerClass(cls, tp, obj, obj.heap(id).asInstanceOf[ObjectRep])
  }

  def init(sym: ClassSymbol, constr: Symbol, valueInfos: List[Value], heap: Heap, obj: ObjectRep, pos: Position): Res = {
    val self = heap(id).asInstanceOf[ObjectRep]
    Rules.init(self, sym, constr, valueInfos, heap, obj, pos)
  }

  override def hashCode = id

  override def equals(that: Any) = that match {
    case that: AtomObjectValue => that.id == id
    case _ => false
  }
}

//=======================================
//           environment
//=======================================

/** Information about fields or local variables */
case class SymInfo(assigned: Boolean = true, forced: Boolean = false, value: Value)

/** The state of closure and objects
  *
  *  @param outerId required for modelling closures
  *
  *  Invariants:
  *  1. the data stored in the immutable map must be immutable
  *  2. environment refer each other via `id`, which implies TransparentValue should
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

  def newObject(heap: Heap = this.heap): ObjectRep = {
    val obj = new ObjectRep
    heap.add(obj)
    obj
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
  def forcedSyms  = _syms.keys.filter(sym => _syms(sym).forced)

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
        _syms = _syms.updated(sym, info.copy(assigned = false, transparentValue = NoTransparent))
      else {
        val infoRes = info.copy(
          assigned   =  true,
          forced     =  info.forced || info2.forced,
          value      =  info.value.join(info2.value)
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
        ~ | lazy forced:  ${forcedSyms}"""
    .stripMargin('~')
}

/** ClassEnv stores the outer information for class members with a particular prefix (outer)
 *
 *  Class environment are immutable, thus they don't need to be in the heap.
 */
case class ClassEnv(envId: Int, val tp: Type) {
  def classSymbol(implicit ctx: Context): ClassSymbol = tp.classSymbol.asClass
}

/** A container holds all information about fields of an object and outers of object's classes
 */
class ObjectRep extends HeapEntry with Cloneable {
  override def clone: ObjectRep = super.clone.asInstanceOf[ObjectRep]

  def fresh: ObjectRep = {
    val obj = new ObjectRep
    obj._fields = this._fields
    obj._classEnvs = this._classEnvs
    heap.add(obj)
    obj
  }

  // in linearization order, last is current class
  private var _classEnvs: Map[Symbol, ClassEnv] = Map()
  def add(sym: Symbol, classEnv: ClassEnv) =
    _classEnvs = _fields.updated(sym, classEnv)

  def classEnv: Map[Symbol, ClassEnv] = _classEnvs

  def tp: Type = _classEnvs.last.tp

  /** Fields of the object, in most cases only field name matters.
   *
   *  Usage of symbols make it possible to support shadowed fields.
   *  Name resolution done elsewhere.
   */
  private var _fields: Map[Symbol, SymInfo] = Map()

  def apply(sym: Symbol): SymInfo =
    _fields(sym)

  def add(sym: Symbol, info: SymInfo) =
    _fields = _fields.updated(sym, info)

  // object environment should not resolve outer
  def update(sym: Symbol, info: SymInfo): Unit = {
    assert(_fields.contains(sym))
    _fields = _fields.updated(sym, info)
  }

  def contains(sym: Symbol): Boolean =
    _fields.contains(sym)

  def isAssigned(sym: Symbol): Boolean =
    _fields(sym).assigned

  def setAssigned(sym: Symbol): Unit =
    _fields = _fields.updated(sym, _fields(sym).copy(assigned = true))

  def notAssigned = _fields.keys.filter(sym => !(_fields(sym).assigned))
  def partialSyms = _fields.keys.filter(sym => _fields(sym).isPartial)
  def filledSyms  = _fields.keys.filter(sym => _fields(sym).isFilled)
  def forcedSyms  = _fields.keys.filter(sym => _fields(sym).forced)
  def transparentSyms  = _fields.keys.filter(sym => _fields(sym).isTransparent)

  def join(obj2: ObjectRep): ObjectRep = {
    assert(this.id == obj2.id)

    _fields.foreach { case (sym: Symbol, info: SymInfo) =>
      assert(obj2.contains(sym))
      val info2 = obj2._fields(sym)
      // path-insensitive approximation:
      // 1. if a variable is assigned in one branch, but not in the other branch, we
      //    treat the variable as not assigned.
      // 2. a lazy variable is force if it's forced in either branch
      // 3. a variable gets the lowest possible state
      if (!info.assigned || !info2.assigned)
        _fields = _fields.updated(sym, info.copy(assigned = false, transparentValue = NoTransparent))
      else {
        val infoRes = info.copy(
          assigned   =  true,
          forced     =  info.forced || info2.forced,
          value      =  info.value.join(info2.value)
        )

        _fields = _fields.updated(sym, infoRes)
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
        ~ | transparent symbols: ${transparentSyms}
        ~ | class: $tp"""
    .stripMargin('~')
}

//=======================================
//           Res
//=======================================
import Effect._

case class Res(var effects: Effects = Vector.empty, var value: Value = OpaqueValue.Full) {
  def +=(eff: Effect): Unit = effects = effects :+ eff
  def ++=(effs: Effects) = effects ++= effs

  def hasErrors  = effects.size > 0

  def join(res2: Res): Res =
    Res(
      effects = res2.effects ++ this.effects,
      value   = res2.value.join(value)
    )

  override def toString: String =
    s"""~Res(
        ~| effects = ${if (effects.isEmpty) "()" else effects.mkString("\n|    - ", "\n|    - ", "")}
        ~| value   = $value
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
    case Transparent(tree, effs)  =>
      ctx.warning(s"Transparent effects results in initialization errors", tree.pos)
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
case class Transparent(tree: tpd.Tree, effs: Seq[Effect]) extends Effect                  // problematic transparent effects (e.g. effects of closures)
case class Generic(msg: String, pos: Position) extends Effect                     // generic problem

object Effect {
  type Effects = Vector[Effect]
}
