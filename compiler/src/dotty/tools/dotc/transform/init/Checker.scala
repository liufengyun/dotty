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

class Checker extends MiniPhase { thisPhase =>
  import tpd._

  override def phaseName: String = Checker.name

  override def transformTypeDef(cdef: TypeDef)(implicit ctx: Context): Tree = {
    if (!ctx.settings.YcheckInit.value || !cdef.isClassDef) return cdef

    val cls = cdef.symbol.asClass
    if (!cls.is(AbstractOrTrait)) {
      debug("*************************************")
      debug("checking " + cls.show)
      new Analyzer(cls).checkTemplate(cls)
      debug("*************************************")
    }

    cdef
  }
}
