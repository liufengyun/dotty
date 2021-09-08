package dotty.tools.dotc
package transform
package init


import dotty.tools.dotc._
import ast.tpd
import tpd._

import dotty.tools.dotc.core._
import Contexts._
import Types._
import Symbols._
import StdNames._

import dotty.tools.dotc.transform._
import Phases._

import scala.collection.mutable

import Semantic._

class Checker extends Phase {

  val phaseName = "initChecker"

  override val runsAfter = Set(Pickler.name)

  override def isEnabled(using Context): Boolean =
    super.isEnabled && ctx.settings.YcheckInit.value

  override def runOn(units: List[CompilationUnit])(using Context): List[CompilationUnit] =
    val checkCtx = ctx.fresh.setPhase(this.start)
    Semantic.withInitialState {
      val traverser = new InitTreeTraverser()
      units.foreach { unit => traverser.traverse(unit.tpdTree) }
      given Context = checkCtx
      Semantic.check()
      super.runOn(units)
    }

  def run(using Context): Unit = {
    // ignore, we already called `Semantic.check()` in `runOn`
  }

  class InitTreeTraverser(using State) extends TreeTraverser {
    override def traverse(tree: Tree)(using Context): Unit =
      traverseChildren(tree)
      tree match {
        case mdef: MemberDef =>
          // self-type annotation ValDef has no symbol
          if mdef.name != nme.WILDCARD then
            mdef.symbol.defTree = tree

          mdef match
          case tdef: TypeDef if tdef.isClassDef =>
            val cls = tdef.symbol.asClass
            val ctor = cls.primaryConstructor
            val args = ctor.defTree.asInstanceOf[DefDef].termParamss.flatten.map(_ => Hot)
            val outer = Hot
            val thisRef = ThisRef(cls, outer, ctor, args)
            given Trace = Trace.empty
            if shouldCheckClass(cls) then Semantic.addTask(thisRef)
          case _ =>

        case _ =>
      }
  }

  private def shouldCheckClass(cls: ClassSymbol)(using Context) = {
    val instantiable: Boolean =
      cls.is(Flags.Module) ||
      !cls.isOneOf(Flags.AbstractOrTrait) && {
        // see `Checking.checkInstantiable` in typer
        val tp = cls.appliedRef
        val stp = SkolemType(tp)
        val selfType = cls.givenSelfType.asSeenFrom(stp, cls)
        !selfType.exists || stp <:< selfType
      }

    // A concrete class may not be instantiated if the self type is not satisfied
    instantiable && cls.enclosingPackageClass != defn.StdLibPatchesPackage.moduleClass
  }
}
