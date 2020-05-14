package dotty.tools.dotc
package transform
package init


import dotty.tools.dotc._
import ast.tpd

import dotty.tools.dotc.core._
import Contexts.Context
import Types._

import dotty.tools.dotc.transform._
import MegaPhase._

import dotty.tools.dotc.util._

import scala.collection.mutable
import scala.collection.immutable

object Checker {
  enum Kind { case ThisCall, ThisAccess, WarmCall, WarmAccess }
  private val data = mutable.Map.empty[Kind, immutable.Set[SourcePosition]].withDefault(k => immutable.Set.empty[SourcePosition])

  def thisCall(pos: SourcePosition) = data(Kind.ThisCall) = data(Kind.ThisCall) + pos
  def thisAccess(pos: SourcePosition) = data(Kind.ThisAccess) = data(Kind.ThisAccess) + pos
  def warmCall(pos: SourcePosition) = data(Kind.WarmCall) = data(Kind.WarmCall) + pos
  def warmAccess(pos: SourcePosition) = data(Kind.WarmAccess) = data(Kind.WarmAccess) + pos

  def report() = {
    println("init-oopsla:this-call:" + data(Kind.ThisCall).size)
    println("init-oopsla:this-access:" + data(Kind.ThisAccess).size)
    println("init-oopsla:warm-call:" + data(Kind.WarmCall).size)
    println("init-oopsla:warm-access:" + data(Kind.WarmAccess).size)

    data.clear()
  }
}

class Checker extends MiniPhase {
  import tpd._

  val phaseName = "initChecker"

  // cache of class summary
  private val baseEnv = Env(null, mutable.Map.empty)

  override val runsAfter = Set(Pickler.name)

  override def isEnabled(implicit ctx: Context): Boolean =
    super.isEnabled && ctx.settings.YcheckInit.value

  override def transformTypeDef(tree: TypeDef)(implicit ctx: Context): tpd.Tree = {
    if (!tree.isClassDef) return tree

    val cls = tree.symbol.asClass
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
    if (instantiable) {
      implicit val state = Checking.State(
        visited = mutable.Set.empty,
        path = Vector.empty,
        thisClass = cls,
        fieldsInited = mutable.Set.empty,
        parentsInited = mutable.Set.empty,
        env = baseEnv.withCtx(ctx)
      )

      val now = System.nanoTime

      Checking.checkClassBody(tree)

      val total = (System.nanoTime - now) / 1000
      println("init-oopsla:init-check-time:" + total)
    }


    tree
  }
}
