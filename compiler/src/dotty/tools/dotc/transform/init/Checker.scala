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
  def constructorCode(cdef: TypeDef)(implicit ctx: Context) = {
    val cls = cdef.symbol
    val tmpl = cdef.rhs.asInstanceOf[Template]
    val stats = tmpl.body.filter {
      case vdef: ValDef =>
        !vdef.symbol.is(ParamAccessor) && !vdef.symbol.is(Lazy) && !vdef.symbol.is(Deferred)
      case _: DefTree => false
      case _          => true
    }
    val statsWithInit = if (cls.is(Trait)) stats else tmpl.parents.head +: stats
    tpd.Block(statsWithInit, tpd.unitLiteral)
  }

  def registerConstructorCode(cdef: TypeDef)(implicit ctx: Context) =
    if (!cdef.symbol.is(Final)) {
      val primCtor = cdef.symbol.primaryConstructor
      val initCode = constructorCode(cdef)
      PrepareInlineable.registerInlineInfo(primCtor, implicit ctx => initCode)(ctx)
    }

  def getConstructorCode(cls: ClassSymbol)(implicit ctx: Context): Tree =
    if (!cls.primaryConstructor.hasAnnotation(defn.BodyAnnot)) EmptyTree
    else Inliner.bodyToInline(cls.primaryConstructor)
}

class Checker extends MiniPhase { thisPhase =>
  override def phaseName: String = Checker.name

  override def transformTypeDef(cdef: TypeDef)(implicit ctx: Context): Tree = {
    if (!ctx.settings.YcheckInit.value || !cdef.isClassDef) return cdef

    val cls = cdef.symbol.asClass
    if (!cls.is(AbstractOrTrait)) {
      debug("*************************************")
      debug("checking " + cls.show)
      val body = Checker.constructorCode(cdef)
      new Analyzer(cls).checkTemplate(cls, body)
      debug("*************************************")
    }

    cdef
  }
}
