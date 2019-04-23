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

  def checkInit(cdef: TypeDef)(implicit ctx: Context): Unit = {
    val cls = cdef.symbol.asClass
    if (cls.is(AbstractOrTrait)) return

    new Analyzer(cls).check(cdef)
  }

  def run(implicit ctx: Context): Unit = {
    if (!ctx.settings.YcheckInit.value) return

    val unit = ctx.compilationUnit
    work(unit.tpdTree)(ctx.fresh.setPhase(this.next))
  }

  def work(tree: Tree)(implicit ctx: Context): Unit = tree match {
    case PackageDef(_, stats) =>
      stats.foreach(stat => work(stat))
    case tree: TypeDef if tree.isClassDef => checkInit(tree)
    case _ =>
  }
}
