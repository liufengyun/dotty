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


trait Indexer { self: Analyzer =>
  import tpd._

  def methodValue(ddef: DefDef, env: Env)(implicit ctx: Context): FunctionValue =
    new FunctionValue {
      def apply(values: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res =
        if (isChecking(ddef.symbol)) {
          // TODO: check if fixed point has reached. But the domain is infinite, thus non-terminating.
          debug(s"recursive call of ${ddef.symbol} found")
          Res()
        }
        else {
          val env2 = env.fresh(heap)

          ddef.vparamss.flatten.zipWithIndex.foreach { case (param: ValDef, index: Int) =>
            env2.add(param.symbol, value = values(index))
          }

          checking(ddef.symbol) { self.apply(ddef.rhs, env2)(ctx.withOwner(ddef.symbol)) }
        }
    }

  def lazyValue(vdef: ValDef, env: Env)(implicit ctx: Context): LazyValue =
    new LazyValue {
      def apply(values: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res =
        if (isChecking(vdef.symbol)) {
          // TODO: check if fixed point has reached. But the domain is infinite, thus non-terminating.
          debug(s"recursive call of ${vdef.symbol} found")
          Res()
        }
        else {
          val env2 = heap(env.id).asEnv
          checking(vdef.symbol) { self.apply(vdef.rhs, env2)(ctx.withOwner(vdef.symbol)) }
        }
    }

  def constructorValue(cls: ClassSymbol, tmpl: Template, env: Env, obj: ObjectRep)(implicit ctx: Context): FunctionValue = {
    val constr: DefDef = tmpl.constr
    new FunctionValue {
      def apply(values: Int => Value, argPos: Int => Position, pos: Position, heap: Heap)(implicit ctx: Context): Res = {
        if (isChecking(cls)) {
          debug(s"recursive creation of $cls found")
          Res()
        }
        else checking(cls) {
          val innerClsEnv = heap(env.id).asInstanceOf[Env]
          val objCurrent = heap(obj.id).asInstanceOf[ObjectRep]

          // an object can only be initialized once
          objCurrent.remove(constr.symbol)

          // setup constructor params
          constr.vparamss.flatten.zipWithIndex.foreach { case (param: ValDef, index: Int) =>
            val sym = cls.info.member(param.name).suchThat(x => !x.is(Method)).symbol
            if (sym.exists) objCurrent.add(sym, values(index))
            innerClsEnv.add(param.symbol, values(index))
          }

          checkTemplate(cls, obj.tp, tmpl, innerClsEnv, obj)
        }
      }
    }
  }

  /** Index local definitions */
  def indexStats(stats: List[Tree], env: Env)(implicit ctx: Context): Unit = stats.foreach {
    case ddef: DefDef if !ddef.symbol.isConstructor =>  // TODO: handle secondary constructor
      env.add(ddef.symbol, methodValue(ddef, env))
    case vdef: ValDef if vdef.symbol.is(Lazy)  =>
      env.add(vdef.symbol, lazyValue(vdef, env))
    case vdef: ValDef =>
      env.add(vdef.symbol, NoValue)
    case tdef: TypeDef if tdef.isClassDef  =>
      // class has to be handled differently because of inheritance
      env.addClassDef(tdef.symbol.asClass, tdef.rhs.asInstanceOf[Template])
    case _ =>
  }

  /** Index member definitions
   *
   *  trick: use `ObjectRep` for name resolution, but `env` for method execution
   */
  def indexMembers(stats: List[Tree], env: Env, obj: ObjectRep)(implicit ctx: Context): Unit = stats.foreach {
    case ddef: DefDef =>
      obj.add(ddef.symbol, methodValue(ddef, env))
    case vdef: ValDef if vdef.symbol.is(Lazy)  =>
      obj.add(vdef.symbol, lazyValue(vdef, env))
    case vdef: ValDef =>
      obj.add(vdef.symbol, NoValue)
    case tdef: TypeDef if tdef.isClassDef  =>
      // class has to be handled differently because of inheritance
      obj.add(tdef.symbol.asClass, tdef.rhs.asInstanceOf[Template] -> env.id)
    case _ =>
  }

  def indexClass(cls: ClassSymbol, tmpl: Template, obj: ObjectRep, env: Env)(implicit ctx: Context): Unit = {
    val innerClsEnv = env.fresh()

    // don't go recursively for parents as indexing is based on linearization
    indexMembers(tmpl.body, innerClsEnv, obj)

    // index primary constructor
    val value = constructorValue(cls, tmpl, innerClsEnv, obj)
    obj.add(tmpl.constr.symbol, value)

    // setup this
    val self =  new ObjectValue(obj.id)
    innerClsEnv.add(cls, self)
  }
}
