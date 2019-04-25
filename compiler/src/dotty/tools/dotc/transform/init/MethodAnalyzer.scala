
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
import Annotations._
import Decorators._
import DenotTransformers._
import config.Printers.init.{ println => debug }
import Constants.Constant
import collection.mutable

/** This transform analyzes initialization effects of methods.
 *
 *  The effects of methods will be annotated as `@Use[T]`
 *
 *  Effects as follows:
 *
 *  - `C.this`: leak of this
 *  - `C.this.f`: field access, possibly dynamic (if `f` is not `private` or `final`)
 *  - `C.this.m`: method call, possibly dynamic
 *  - `C.super.m`: method call, possibly dynamic
 *  - `C.super[D].m`: method call, possibly dynamic
 *  - `C.this.D`: inner class instantiation
 *  - `C.this.D.<init>`: constructor call, only used as effects of constructors
 *
 */
class MethodAnalyzer extends MiniPhase with IdentityDenotTransformer { thisPhase =>
  import tpd._

  override def phaseName: String = MethodAnalyzer.name

  override def transformDefDef(tree: DefDef)(implicit ctx: Context): Tree = {
    // don't analyze inline methods, as the calls to inline methods will disappear after inlining
    if (tree.symbol.is(Deferred) || tree.symbol.is(InlineMethod)) return tree

    val methSym  = tree.symbol
    val analysis = new MethodAnalyzer.CaptureAnalysis(methSym)
    val frees = analysis(Set.empty, tree.rhs)

    debug("effects of " + methSym.show + ": " + frees.map(_.show).mkString(", "))

    frees.foreach { tp => methSym.addAnnotation(Annotation.Use(tp)) }

    tree
  }
}

object MethodAnalyzer {
  import tpd._

  val name = "methodAnalyzer"

  private class CaptureAnalysis(methSym: Symbol) extends TreeAccumulator[Set[Type]] {

    def free(tp: Type)(implicit ctx: Context): Boolean = tp.dealias match {
      case tp : TermRef if tp.symbol.is(Module) && ctx.owner.isContainedIn(tp.symbol.moduleClass) =>
        // self reference by name: object O { ... O.xxx }
        free(ThisType.raw(tp.symbol.moduleClass.typeRef))
      case tp @ TermRef(ThisType(tref), _) =>
        val cls = tref.symbol
        // ThisType used outside of class scope, can happen for objects
        // see tests/pos/t2712-7.scala
        !cls.is(Package) && !(cls.is(Flags.Module) || cls.isContainedIn(methSym))
      case _ =>
        false
    }

    def apply(res: Set[Type], tree: Tree)(implicit ctx: Context) =
      tree match {
        case tree if tree.isType =>
          // ignore all type trees
          res
        case _: Ident if tree.symbol.isTerm =>
          if (free(tree.tpe)) res + tree.tpe
          else res
        case _: This =>
          res + tree.tpe
        case Select(_: Super, _) =>
          res + tree.tpe
        case Select(thist: This, _) =>
          res + tree.tpe
        case Select(qualifier, _) =>
          if (free(tree.tpe)) res + tree.tpe
          else if (free(qualifier.tpe)) res + qualifier.tpe
          else res
        // case tree @ Assign(sel: Select, rhs) =>
        //   annotate(sel, rhs)
        // case tree: New =>
        //   annotate(tree)
        case _ =>
          foldOver(res, tree)
      }
  }
}
