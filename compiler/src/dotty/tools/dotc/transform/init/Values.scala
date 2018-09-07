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
//             values
//=======================================

object Value {
  def checkParams(paramInfos: List[Type], values: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res = {
    paramInfos.zipWithIndex.foreach { case (tp, index: Int) =>
      val value = values(index)
      val pos = argPos(index)
      if (value.widen(heap, pos) < tp.value)
        return Res(effects = Vector(Generic("Leak of object under initialization", pos)))
    }
    Res()
  }

  def defaultFunctionValue(methSym: Symbol)(implicit ctx: Context): Value = {
    new FunctionValue() {
      def apply(values: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res = {
        val paramInfos = methSym.info.paramInfoss.flatten
        checkParams(paramInfos, values, argPos, pos, heap)
      }
    }
  }
}

/** Abstract values in analysis */
sealed trait Value {
  /** Select a member on a value */
  def select(sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res

  /** Assign on a value */
  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position)(implicit ctx: Context): Res

  /** Index an inner class with current value as the immediate outer */
  def init(constr: Symbol, values: List[Value], argPos: List[Position], pos: Position, obj: ObjectValue, heap: Heap, indexer: Indexer)(implicit ctx: Context): Res

  /** Apply a method or function to the provided arguments */
  def apply(values: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res

  /** Join two values
   *
   *  NoValue < Partial < Filled < Full
   */
  def join(other: Value): Value = (this, other) match {
    case (FullValue, v) => v
    case (v, FullValue) => v
    case (NoValue, _) => NoValue
    case (_, NoValue) => NoValue
    case (PartialValue, _) => NoValue
    case (_, PartialValue) => NoValue
    case (v1: OpaqueValue, v2: OpaqueValue)     => v1.join(v2)
    case (m1: FunctionValue, m2: FunctionValue) => UnionValue(Set(m1, m2))
    case (o1: SliceValue, o2: SliceValue) =>
      if (o1.id == o2.id) o1
      else new UnionValue(Set(o1, o2))
    case (v1: UnionValue, v2: UnionValue) => v1 ++ v2
    case (uv: UnionValue, v: SingleValue) => uv + v
    case (v: SingleValue, uv: UnionValue) => uv + v
    case (v1: SingleValue, v2: SingleValue) => UnionValue(Set(v1, v2))
    case _ =>
      throw new Exception(s"Can't join $this and $other")
  }

  /** Widen the value to an opaque value
   *
   *  Widening is needed at analysis boundary.
   */
  def widen(heap: Heap, pos: Position)(implicit ctx: Context): OpaqueValue = {
    val testHeap = heap.clone
    def recur(value: Value): OpaqueValue = value match {
      case ov: OpaqueValue => ov
      case fv: FunctionValue =>
        val res = fv(i => FullValue, i => NoPosition, pos, testHeap)
        if (res.hasErrors) FilledValue
        else recur(res.value)
      case sv: SliceValue =>
        val slice = heap(sv.id).asSlice
        if (slice.classInfos.nonEmpty) FilledValue
        else slice.symbols.values.foldLeft(FullValue: OpaqueValue) { (acc, v) =>
          v.widen(heap, pos).join(acc)
        }
      case ov: ObjectValue =>
        if (!ov.init) PartialValue
        else ov.slices.values.foldLeft(FullValue: OpaqueValue) { (acc, v) =>
          v.widen(heap, pos).join(acc)
        }
      case UnionValue(vs) =>
        vs.foldLeft(FullValue: OpaqueValue) { (acc, v) =>
          if (v == PartialValue) return PartialValue
          else acc.join(recur(v))
        }
      case _ => // impossible
        ???
    }

    recur(this)
  }
}

/** The value is absent */
object NoValue extends Value {
  def apply(values: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res = ???
  def select(sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res = ???
  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position)(implicit ctx: Context): Res = ???
  def init(constr: Symbol, values: List[Value], argPos: List[Position], pos: Position, obj: ObjectValue, heap: Heap, indexer: Indexer)(implicit ctx: Context): Res = ???
}

/** A single value, instead of a union value */
sealed trait SingleValue extends Value

/** Union of values */
case class UnionValue(val values: Set[SingleValue]) extends Value {
  def apply(args: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res = {
    values.foldLeft(Res()) { (acc, value) =>
      value.apply(args, argPos, pos, heap).join(acc)
    }
  }

  def select(sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    values.foldLeft(Res()) { (acc, value) =>
      value.select(sym, heap, pos).join(acc)
    }
  }

  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    values.foldLeft(Res()) { (acc, value) =>
      value.assign(sym, value, heap, pos).join(acc)
    }
  }

  def init(constr: Symbol, values: List[Value], argPos: List[Position], pos: Position, obj: ObjectValue, heap: Heap, indexer: Indexer)(implicit ctx: Context): Res = {
    values.foldLeft(Res()) { (acc, value) =>
      value.init(constr, values, argPos, pos, obj, heap, indexer).join(acc)
    }
  }

  def +(value: SingleValue): UnionValue = UnionValue(values + value)
  def ++(uv: UnionValue): UnionValue = UnionValue(values ++ uv.values)
}

/** Values that are subject to type checking rather than analysis */
abstract sealed class OpaqueValue extends SingleValue {
  // not supported
  def apply(values: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res = ???

  def <(that: OpaqueValue): Boolean = (this, that) match {
    case (FullValue, _) => false
    case (FilledValue, PartialValue | FilledValue) => false
    case (PartialValue, PartialValue) => false
    case _ => true
  }

  def join(that: OpaqueValue): OpaqueValue =
    if (this < that) this else that

  def meet(that: OpaqueValue): OpaqueValue =
    if (this < that) that else this
}

object FullValue extends OpaqueValue {
  def select(sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res =
    if (sym.is(Flags.Method)) Res(value = Value.defaultFunctionValue(sym))
    else Res()

  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position)(implicit ctx: Context): Res =
    if (value.widen(heap, pos) != FullValue)
      Res(effects = Vector(Generic("Cannot assign an object under initialization to a full object", pos)))
    else Res()

  def init(constr: Symbol, values: List[Value], argPos: List[Position], pos: Position, obj: ObjectValue, heap: Heap, indexer: Indexer)(implicit ctx: Context): Res = {
    val cls = constr.owner.asClass
    val paramInfos = constr.info.paramInfoss.flatten
    val res = Value.checkParams(paramInfos, values, argPos, pos, heap)
    if (res.hasErrors) return res

    val args = (0 until paramInfos.size).map(values)
    if (args.exists(_.widen(heap, pos) < FullValue)) obj.add(cls, FilledValue)
    else obj.add(cls, FullValue)

    Res()
  }
}

object PartialValue extends OpaqueValue {
  def select(sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    // set state to Full, don't report same error message again
    val res = Res(value = FullValue)

    if (sym.is(Flags.Method)) {
      if (!sym.isPartial)
        res += Generic(s"The $sym should be marked as `@partial` in order to be called", pos)

      res.value = Value.defaultFunctionValue(sym)
    }
    else if (sym.is(Flags.Lazy)) {
      if (!sym.isPartial)
        res += Generic(s"The lazy field $sym should be marked as `@partial` in order to be accessed", pos)
    }
    else if (sym.isClass) {
      if (!sym.isPartial)
        res += Generic(s"The nested $sym should be marked as `@partial` in order to be instantiated", pos)
    }
    else {  // field select
      if (!sym.isPrimaryConstructorFields || sym.owner.is(Flags.Trait))
        res += Generic(s"Cannot access field $sym on a partial object", pos)
    }

    res
  }

  /** assign to partial is always fine? */
  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position)(implicit ctx: Context): Res = Res()

  def init(constr: Symbol, values: List[Value], argPos: List[Position], pos: Position, obj: ObjectValue, heap: Heap, indexer: Indexer)(implicit ctx: Context): Res = {
    val paramInfos = constr.info.paramInfoss.flatten
    val res = Value.checkParams(paramInfos, values, argPos, pos, heap)
    if (res.hasErrors) return res

    val cls = constr.owner.asClass
    if (!cls.isPartial) {
      res += Generic(s"The nested $cls should be marked as `@partial` in order to be instantiated", pos)
      res.value = FullValue
      return res
    }

    obj.add(cls, FilledValue)

    Res()
  }
}

object FilledValue extends OpaqueValue {
  def select(sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    val res = Res()
    if (sym.is(Flags.Method)) {
      if (!sym.isPartial && !sym.isFilled)
        res += Generic(s"The $sym should be marked as `@partial` or `@filled` in order to be called", pos)

      res.value = Value.defaultFunctionValue(sym)
    }
    else if (sym.is(Flags.Lazy)) {
      if (!sym.isPartial && !sym.isFilled)
        res += Generic(s"The lazy field $sym should be marked as `@partial` or `@filled` in order to be accessed", pos)

      res.value = sym.info.value
    }
    else {
      res.value = sym.info.value
    }

    res
  }

  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position)(implicit ctx: Context): Res =
    if (value.widen(heap, pos) < sym.info.value)
      Res(effects = Vector(Generic("Cannot assign an object of a lower state to a field of higher state", pos)))
    else Res()

  def init(constr: Symbol, values: List[Value], argPos: List[Position], pos: Position, obj: ObjectValue, heap: Heap, indexer: Indexer)(implicit ctx: Context): Res = {
    val paramInfos = constr.info.paramInfoss.flatten
    val res = Value.checkParams(paramInfos, values, argPos, pos, heap)
    if (res.hasErrors) return res

    val cls = constr.owner.asClass
    if (!cls.isPartial && !cls.isFilled) {
      res += Generic(s"The nested $cls should be marked as `@partial` or `@filled` in order to be instantiated", pos)
      res.value = FullValue
      return res
    }

    obj.add(cls, FilledValue)

    Res()
  }
}

/** A function value or value of method select */
abstract class FunctionValue extends SingleValue {
  def apply(values: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res

  def select(sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    assert(sym.name.toString == "apply")
    Res(value = this)
  }

  /** not supported */
  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position)(implicit ctx: Context): Res = ???
  def init(constr: Symbol, values: List[Value], argPos: List[Position], pos: Position, obj: ObjectValue, heap: Heap, indexer: Indexer)(implicit ctx: Context): Res = ???
}

/** A lazy value */
abstract class LazyValue extends Value {
  // not supported
  def select(sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res = ???
  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position)(implicit ctx: Context): Res = ???
  def init(constr: Symbol, values: List[Value], argPos: List[Position], pos: Position, obj: ObjectValue, heap: Heap, indexer: Indexer)(implicit ctx: Context): Res = ???
}

/** A slice of an object */
class SliceValue(val id: Int) extends SingleValue {
  /** not supported, impossible to apply an object value */
  def apply(values: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res = ???

  def select(sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    val slice = heap(id).asSlice
    val value = slice(sym)

    if (sym.is(Flags.Lazy)) {
      if (value.isInstanceOf[LazyValue]) {
        val res = value(Nil, Nil, pos, heap)
        slice(sym) = res.value

        if (res.hasErrors) Res(effects = Vector(Force(sym, res.effects, pos)))
        else Res(value = res.value)
      }
      else Res(value = value)
    }
    else if (sym.is(Flags.Method)) {
      if (sym.info.isInstanceOf[ExprType]) {       // parameter-less call
        val res2 = value(Nil, Nil, pos, heap)

        if (res2.effects.nonEmpty)
          res2.effects = Vector(Call(sym, res2.effects, pos))

        res2
      }
      else Res(value = value)
    }
    else {
      var effs = Vector.empty[Effect]
      if (value == NoValue) effs = effs :+ Uninit(sym, pos)

      val res = Res(effects = effs, value = value)

      if (sym.is(Flags.Deferred) && !sym.hasAnnotation(defn.InitAnnot))
        res += UseAbstractDef(sym, pos)

      res
    }
  }

  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    val slice = heap(id).asSlice
    slice(sym) = value
    Res()
  }

  def init(constr: Symbol, values: List[Value], argPos: List[Position], pos: Position, obj: ObjectValue, heap: Heap, indexer: Indexer)(implicit ctx: Context): Res = {
    val cls = constr.owner.asClass
    val slice = heap(id).asSlice
    val tmpl = slice.classInfos(cls)
    indexer.init(constr, tmpl, values, argPos, pos, obj, slice.innerEnv)
  }

  override def hashCode = id

  override def equals(that: Any) = that match {
    case that: SliceValue => that.id == id
    case _ => false
  }
}

class ObjectValue(val tp: Type, var init: Boolean = false, val open: Boolean = false) extends SingleValue {
  /** slices of the object */
  private var _slices: Map[ClassSymbol, Value] = Map()
  def slices: Map[ClassSymbol, Value] = _slices

  def add(cls: ClassSymbol, value: Value) = {
    if (slices.contains(cls)) {
      _slices = _slices.updated(cls, _slices(cls).join(value))
    }
    else _slices = _slices.updated(cls, value)
  }

  // handle dynamic dispatch
  private def resolve(sym: Symbol)(implicit ctx: Context): Symbol = {
    if (sym.isClass || sym.isConstructor || sym.isEffectivelyFinal || sym.is(Flags.Private)) sym
    else sym.matchingMember(tp)
  }

  /** not supported, impossible to apply an object value */
  def apply(values: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res = ???

  def select(sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    val target = resolve(sym)
    val cls = target.owner.asClass
    if (slices.contains(cls)) {
      val res = slices(cls).select(target, heap, pos)
      // ignore field access, but field access in Scala
      // are method calls, thus is unsafe as well
      if (open && target.is(Flags.Method) &&
          !target.hasAnnotation(defn.PartialAnnot) &&
          !target.hasAnnotation(defn.FilledAnnot) &&
          !target.isEffectivelyFinal)
        res += OverrideRisk(target, pos)
      res
    }
    else {
      // two cases: (1) select on unknown super; (2) select on self annotation
      if (target.isDefinedOn(tp)) FilledValue.select(target, heap, pos)
      else PartialValue.select(target, heap, pos)
    }
  }

  def assign(sym: Symbol, value: Value, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    val target = resolve(sym)
    val cls = target.owner.asClass
    if (slices.contains(cls)) {
      slices(cls).assign(target, value, heap, pos)
    }
    else {
      // two cases: (1) select on unknown super; (2) select on self annotation
      if (target.isDefinedOn(tp)) FilledValue.assign(target, value, heap, pos)
      else PartialValue.assign(target, value, heap, pos)
    }
  }

  def init(constr: Symbol, values: List[Value], argPos: List[Position], pos: Position, obj: ObjectValue, heap: Heap, indexer: Indexer)(implicit ctx: Context): Res = {
    val cls = constr.owner.asClass
    val outerCls = cls.owner.asClass
    if (slices.contains(outerCls)) {
      if (this.widen(heap, pos) < FullValue) obj.add(cls, FilledValue)
      slices(outerCls).init(constr, values, argPos, pos, obj, heap, indexer)
    }
    else {
      val value = if (cls.isDefinedOn(tp)) FilledValue else PartialValue
      value.init(constr, values, argPos, pos, obj, heap, indexer)
    }
  }
}
