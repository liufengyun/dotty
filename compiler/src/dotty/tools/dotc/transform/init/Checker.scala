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
import tpd._
import typer._
import Flags._
import SymUtils._
import Symbols._
import Denotations._
import SymDenotations._
import Types._
import Annotations._
import Decorators._
import DenotTransformers._
import config.Printers.init.{ println => debug }
import Constants.Constant
import collection.mutable

object Checker {
  val name = "initChecker"

  /** Executable code in class body
   *
   *  Lazy val, methods and inner classes are summarized by effects,
   *  thus are not memorized.
   *
   * Remember parent calls for classes:
   *   1. which parent constructor is called
   */
  def constructorCode(cls: Symbol, tmpl: Template)(implicit ctx: Context) = {
    val stats = tmpl.body.filter {
      case vdef: ValDef =>
        !vdef.symbol.is(ParamAccessor) && !vdef.symbol.is(Lazy) && !vdef.symbol.is(Deferred)
      case _: DefTree => false
      case _          => true
    }
    tpd.Block(stats, tpd.unitLiteral)
  }

  def registerConstructorCode(cdef: TypeDef)(implicit ctx: Context) =
    if (!cdef.symbol.is(Final)) {
      val cls = cdef.symbol
      val tmpl = cdef.rhs.asInstanceOf[Template]
      val initCode = constructorCode(cdef.symbol, tmpl)
      cls.addAnnotation(Annotations.ConcreteBodyAnnotation(initCode))
      // remember the super constructor called
      if (!cls.is(Trait)) {
        val superCtor = constructorSymbol(tmpl.parents.head)
        cls.primaryConstructor.addAnnotation(Annotation.Use(superCtor.termRef))
      }
    }

  def getConstructorCode(cls: ClassSymbol)(implicit ctx: Context): Tree =
    if (!cls.hasAnnotation(defn.BodyAnnot)) EmptyTree
    else Inliner.bodyToInline(cls)

  def getSuperConstructor(cls: ClassSymbol)(implicit ctx: Context): Symbol =
    cls.primaryConstructor.uses match {
      case (tp: TermRef) :: _ => tp.symbol
      case _                  => NoSymbol
    }

  private def constructorSymbol(tree: Tree)(implicit ctx: Context): Symbol = tree match {
    case NewEx(_, sym, _) => sym
    case _ => tree.symbol.primaryConstructor
  }

  object NewEx {
    def extract(tp: Type)(implicit ctx: Context): TypeRef = tp.dealias match {
      case tref: TypeRef => tref
      case AppliedType(tref: TypeRef, targs) => tref
      case hktp: HKTypeLambda => extract(hktp.hkResult)
    }

    def unapply(tree: Tree)(implicit ctx: Context): Option[(TypeRef, Symbol, List[List[Tree]])] = tree match {
      case Block(_, expr) => unapply(expr)
      case _ =>
        val (fn, targs, vargss) = tpd.decomposeCall(tree)
        if (!fn.symbol.isConstructor || !tree.isInstanceOf[Apply]) None
        else {
          val Select(New(tpt), _) = fn
          Some((extract(tpt.tpe),  fn.symbol, vargss))
        }
    }
  }
}

class Checker extends MiniPhase { thisPhase =>
  override def phaseName: String = Checker.name

  override def transformTypeDef(cdef: TypeDef)(implicit ctx: Context): Tree = {
    if (!ctx.settings.YcheckInit.value || !cdef.isClassDef) return cdef

    val cls = cdef.symbol.asClass
    if (!cls.is(AbstractOrTrait)) {
      debug("*************************************")
      debug("checking " + cls.show)
      val tmpl = cdef.rhs.asInstanceOf[Template]
      val body = Checker.constructorCode(cdef.symbol, tmpl)
      new Analyzer(cls).checkTemplate(cls, Checker.constructorSymbol(tmpl.parents.head), body)
      debug("*************************************")
    }

    cdef
  }
}
