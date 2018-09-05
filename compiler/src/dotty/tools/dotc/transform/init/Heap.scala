package dotty.tools.dotc
package transform
package init

import core._
import Contexts.Context
import StdNames._
import Names._
import ast._
import tpd._
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

  def asEnv: Env = this.asInstanceOf[Env]
  def asSlice: SliceRep = this.asInstanceOf[SliceRep]
}

object Heap {
  private var _uniqueId = 0
  def uniqueId: Int = {
    _uniqueId += 1
    _uniqueId
  }

  class RootEnv extends Env(-1) {
    override def contains(sym: Symbol): Boolean = _syms.contains(sym)

    override def containsClass(cls: ClassSymbol): Boolean =
      _classInfos.contains(cls)
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
    case (s1: SliceRep, s2: SliceRep) => // caller ensures `s1.id = s2.id`
      s1.join(s2)
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
//           environment
//=======================================

/** The state of closure and objects
 *
 *  @param outerId required for modelling closures
 *
 *  Invariants:
 *  1. the data stored in the immutable map must be immutable
 *  2. environment refer each other via `id`, which implies values should
 *     never use captured environment other than its `id`.
 */
class Env(outerId: Int) extends HeapEntry {
  assert(outerId != id)

  /** local symbols defined in current scope */
  protected var _syms: Map[Symbol, Value] = Map()

  /** local class definitions */
  protected var _classInfos: Map[ClassSymbol, Template] = Map()
  def addClassDef(cls: ClassSymbol, tmpl: Template) =
    _classInfos = _classInfos.updated(cls, tmpl)
  def containsClass(cls: ClassSymbol): Boolean =
    _classInfos.contains(cls) || outer.containsClass(cls)
  def getClassDef(cls: ClassSymbol): Template =
    if (_classInfos.contains(cls)) _classInfos(cls)
    else outer.getClassDef(cls)

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

  def newSlice(tp: Type, heap: Heap = this.heap): SliceRep = {
    val innerEnv = fresh(heap)
    val slice = new SliceRep(tp, innerEnvId = innerEnv.id)
    heap.add(slice)
    slice
  }

  def apply(sym: Symbol): Value =
    if (_syms.contains(sym)) _syms(sym)
    else outer(sym)

  def add(sym: Symbol, value: Value) =
    _syms = _syms.updated(sym, value)

  def update(sym: Symbol, value: Value): Unit =
    if (_syms.contains(sym)) _syms = _syms.updated(sym, value)
    else outer.update(sym, value)

  def contains(sym: Symbol): Boolean = _syms.contains(sym) || outer.contains(sym)

  def notAssigned = _syms.keys.filter(sym => _syms(sym) == NoValue)
  def notForcedSyms  = _syms.keys.filter(sym => _syms(sym).isInstanceOf[LazyValue])

  def join(env2: Env): Env = {
    assert(this.id == env2.id)

    _syms.foreach { case (sym: Symbol, value: Value) =>
      assert(env2.contains(sym))
      val value2 = env2._syms(sym)
      _syms = _syms.updated(sym, value.join(value2))
    }

    this
  }

  /** Assign to a local variable, i.e. TermRef with NoPrefix */
  def assign(sym: Symbol, value: Value, pos: Position)(implicit ctx: Context): Res =
    if (this.contains(sym)) {
      this(sym) = value
      Res()
    }
    else if (value.widen(this.heap, pos) != FullValue) // leak assign
      Res(effects = Vector(Generic("Cannot leak an object under initialization", pos)))
    else Res()


  /** Select a local variable, i.e. TermRef with NoPrefix */
  def select(sym: Symbol, pos: Position)(implicit ctx: Context): Res =
    if (this.contains(sym)) {
      val value = this(sym)
      if (sym.is(Flags.Lazy)) {
        if (value.isInstanceOf[LazyValue]) {
          val res = value(Nil, Nil, pos, this.heap)
          this(sym) = res.value

          if (res.hasErrors) Res(effects = Vector(Force(sym, res.effects, pos)))
          else Res(value = res.value)
        }
        else Res(value = value)
      }
      else if (sym.is(Flags.Method)) {
        if (sym.info.isInstanceOf[ExprType]) {       // parameter-less call
          val res2 = value(Nil, Nil, pos, this.heap)

          if (res2.effects.nonEmpty)
            res2.effects = Vector(Call(sym, res2.effects, pos))

          res2
        }
        else Res(value = value)
      }
      else {
        var effs = Vector.empty[Effect]
        if (value == NoValue) Res(effects = effs :+ Uninit(sym, pos))
        else Res(value = value)
      }
    }
    else if (sym.isClass && this.containsClass(sym.asClass)) Res()
    else {
      // How do we know the class/method/field does not capture/use a partial/filled outer?
      // If method/field exist, then the outer class beyond the method/field is full,
      // i.e. external methods/fields/classes are always safe.
      Res()
    }

  def init(constr: Symbol, values: List[Value], argPos: List[Position], pos: Position, obj: ObjectValue, indexer: Indexer)(implicit ctx: Context): Res = {
    val cls = constr.owner.asClass
    if (this.containsClass(cls)) {
      val tmpl = this.getClassDef(cls)
      indexer.init(constr, tmpl, values, argPos, pos, obj, this)
    }
    else FullValue.init(constr, values, argPos, pos, obj, indexer)
  }

  override def toString: String =
    (if (outerId > 0) outer.toString + "\n" else "") ++
    s"""~ -------------- $id($outerId) ---------------------
        ~ | locals:  ${_syms.keys}
        ~ | not initialized:  ${notAssigned}
        ~ | lazy not forced:  ${notForcedSyms}"""
    .stripMargin('~')
}

/** A container holds all information about fields of an class slice of an object
 */
class SliceRep(val tp: Type, innerEnvId: Int) extends HeapEntry with Cloneable {
  override def clone: SliceRep = super.clone.asInstanceOf[SliceRep]

  def innerEnv: Env = heap(innerEnvId).asEnv

  /** inner class definitions */
  private var _classInfos: Map[ClassSymbol, Template] = Map()
  def add(cls: ClassSymbol, info: Template) = _classInfos =
    _classInfos.updated(cls, info)
  def classInfos: Map[ClassSymbol, Template] = _classInfos

  /** methods and fields of the slice */
  private var _syms: Map[Symbol, Value] = Map()

  def apply(sym: Symbol): Value =
    _syms(sym)

  def add(sym: Symbol, value: Value) =
    _syms = _syms.updated(sym, value)

  def remove(sym: Symbol) =
    _syms = _syms - sym

  def update(sym: Symbol, value: Value): Unit = {
    assert(_syms.contains(sym))
    _syms = _syms.updated(sym, value)
  }

  def contains(sym: Symbol): Boolean =
    _syms.contains(sym)

  def notAssigned = _syms.keys.filter(sym => _syms(sym) == NoValue)
  def notForcedSyms  = _syms.keys.filter(sym => _syms(sym).isInstanceOf[LazyValue])

  // Invariant: two slices with the same id always have the same `classInfos`,
  //            thus they can be safely ignored in `join`.
  def join(obj2: SliceRep): SliceRep = {
    assert(this.id == obj2.id)

    _syms.foreach { case (sym: Symbol, value: Value) =>
      assert(obj2.contains(sym))
      val value2 = obj2._syms(sym)
      _syms = _syms.updated(sym, value.join(value2))
    }

    this
  }

  override def equals(that: Any): Boolean = that match {
    case that: SliceRep => that.id == this.id
    case _ => false
  }

  override def toString: String =
    s"""~ --------------${id}---------------------
        ~ | fields:  ${_syms.keys}
        ~ | not initialized:  ${notAssigned}
        ~ | lazy not forced:  ${notForcedSyms}
        ~ | class: $tp"""
    .stripMargin('~')
}
