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
import config.Printers.init.{ println => debug }
import Constants.Constant
import collection.mutable

class Analyzer { analyzer =>
  import tpd._

  type Res = Set[Type]

  def checkApply(tree: Tree, fun: Tree, argss: List[List[Tree]])(implicit ctx: Context): Res = ???

  def checkSelect(tree: Select)(implicit ctx: Context): Res = ???

  def checkRef(tp: Type, widening: Boolean = false)(implicit ctx: Context): Res = ???

  def checkClosure(sym: Symbol, tree: Tree)(implicit ctx: Context): Res = ???

  def checkIf(tree: If)(implicit ctx: Context): Res = ???

  def checkValDef(vdef: ValDef)(implicit ctx: Context): Res = ???

  def checkStats(stats: List[Tree])(implicit ctx: Context): Res = ???

  def checkBlock(tree: Block)(implicit ctx: Context): Res = ???

  def checkAssign(lhs: Tree, rhs: Tree)(implicit ctx: Context): Res = ???

  /** Check a parent call */
  def checkInit(tp: Type, init: Symbol, argss: List[List[Tree]])(implicit ctx: Context): Res = ???

  def checkParents(cls: ClassSymbol, parents: List[Tree])(implicit ctx: Context): Res = ???

  def checkNew(tree: Tree, tref: TypeRef, init: Symbol, argss: List[List[Tree]])(implicit ctx: Context): Res = ???

  def checkSuper(tree: Tree, supert: Super)(implicit ctx: Context): Res = ???

  object NewEx {
    def extract(tp: Type)(implicit ctx: Context): TypeRef = tp.dealias match {
      case tref: TypeRef => tref
      case AppliedType(tref: TypeRef, targs) => tref
    }

    def unapply(tree: Tree)(implicit ctx: Context): Option[(TypeRef, Symbol, List[List[Tree]])] = {
      val (fn, targs, vargss) = tpd.decomposeCall(tree)
      if (!fn.symbol.isConstructor || !tree.isInstanceOf[Apply]) None
      else {
        val Select(New(tpt), _) = fn
        Some((extract(tpt.tpe),  fn.symbol, vargss))
      }
    }
  }


  def apply(tree: Tree)(implicit ctx: Context): Res = tree match {
    case vdef : ValDef if !vdef.symbol.is(Lazy) && !vdef.rhs.isEmpty =>
      checkValDef(vdef)
    case _: DefTree =>
      Set.empty
    case Closure(_, meth, _) =>
      checkClosure(meth.symbol, tree)
    case tree: Ident if tree.symbol.isTerm =>
      checkRef(tree.tpe)
    case tree: This =>
      checkRef(tree.tpe)
    case tree @ Select(supert: Super, _) =>
      checkSuper(tree, supert)
    case tree: Select if tree.symbol.isTerm =>
      checkSelect(tree)
    case tree: If =>
      checkIf(tree)
    case tree @ NewEx(tref, init, argss) => // must before Apply
      checkNew(tree, tref, init, argss)
    case tree: Apply =>
      val (fn, targs, vargss) = decomposeCall(tree)
      checkApply(tree, fn, vargss)
    case tree @ Assign(lhs, rhs) =>
      checkAssign(lhs, rhs)
    case tree: Block =>
      checkBlock(tree)
    case Typed(expr, tpt) =>
      apply(expr)
    case Inlined(call, bindings, expansion) =>
      checkBlock(Block(bindings, expansion))
    case _ =>
      Set.empty
  }
}