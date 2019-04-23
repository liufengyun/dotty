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

object Checker {
  val name = "initChecker"
}

class Checker extends Phase { thisPhase =>
  import tpd._

  override def phaseName: String = Checker.name

  def transformTypeDef(tree: TypeDef)(implicit ctx: Context): Tree = {
    if (!tree.isClassDef) return tree

    val cls = tree.symbol.asClass
    val skipCheck =  cls.is(AbstractOrTrait) || cls.hasAnnotation(defn.UncheckedAnnot)
    if (skipCheck) return tree

    checkInit(cls, tree)

    tree
  }

  def run(implicit ctx: Context): Unit = {
    if (!ctx.settings.YcheckInit.value) return

    val unit = ctx.compilationUnit
    println(unit.tpdTree)
    ctx.fresh.setPhase(this.next)
  }

  def checkInit(cls: ClassSymbol, cdef: tpd.TypeDef)(implicit ctx: Context) = {
    val tmpl = cdef.rhs.asInstanceOf[tpd.Template]

    debug("*************************************")
    debug("checking " + cls.show)
    debug("*************************************")
  }
}
