
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
class CaptureAnalyzer extends MiniPhase with IdentityDenotTransformer { thisPhase =>
  import tpd._

  override def phaseName: String = CaptureAnalyzer.name

  override def transformTypeDef(cdef: TypeDef)(implicit ctx: Context): Tree = {
    if (!cdef.isClassDef) return cdef

    val cls = cdef.symbol.asClass
    val tmpl @ Template(constr, parents, _, _) = cdef.rhs

    // TODO: optimize performance with only one pass
    // Not a problem in practice, as class definitions are shallow
    def analyze(sym: Symbol, tree: Tree) = {
      val analysis = new CaptureAnalyzer.CaptureAnalysis(cls)
      val frees = analysis(Set.empty, tree)

      debug("effects of " + sym.show + ": " + frees.map(_.show).mkString(", "))

      frees.foreach { tp => sym.addAnnotation(Annotation.Use(tp)) }
    }

    tmpl.body.foreach {
      case vdef: ValDef if vdef.symbol.is(Lazy) && !vdef.symbol.is(Deferred) =>
        analyze(vdef.symbol, vdef.rhs)
      case ddef: DefDef if !ddef.symbol.is(Deferred) && !ddef.symbol.is(InlineMethod) =>
        // don't distinguish effects of constructor on its outer
        analyze(ddef.symbol, ddef.rhs)
      case cdef: TypeDef if cdef.isClassDef =>
        // approximate inner class effects on its immediate outer
        analyze(cdef.symbol, cdef)
      case _ =>
    }

    // link class body to symbol via annotation
    Checker.registerConstructorCode(cdef)

    cdef
  }
}

object CaptureAnalyzer {
  import tpd._

  val name = "captureAnalyzer"

  class CaptureAnalysis(on: Symbol) extends TreeAccumulator[Set[Type]] {
    def free(tp: Type)(implicit ctx: Context): Boolean = tp.dealias match {
      case TermRef(tp : TermRef, _) =>
        tp.symbol.is(Module) && tp.symbol.moduleClass == on
      case TypeRef(tp : TermRef, _) =>
        tp.symbol.is(Module) && tp.symbol.moduleClass == on
      case TermRef(ThisType(tref), _) => tref.symbol == on
      case TypeRef(ThisType(tref), _) => tref.symbol == on
      case ThisType(tref) => tref.symbol == on
      case _ => false
    }

    def addIfFree(res: Set[Type], tp: Type)(implicit ctx: Context) =
      if (free(tp)) res + tp
      else res

    def addPart(res: Set[Type], tp: Type)(implicit ctx: Context): Set[Type] =
      // cannot use the following, as it goes to underlying
      // tp.namedPartsWith(ntp => free(ntp), excludeLowerBounds = true).toSet
      new TypeAccumulator[Set[Type]] {
        def apply(res: Set[Type], tp: Type) =
          if (free(tp)) res + tp else foldOver(res, tp)
      }.apply(res, tp)

    def apply(res: Set[Type], tree: Tree)(implicit ctx: Context) =
      tree match {
        case tree if tree.isType =>
          // ignore all type trees
          res
        case _: Import =>
          res
        case _: Ident if tree.symbol.isTerm =>
          addPart(res, tree.tpe)
        case _: This | Select(_: Super, _) | Select(_: This, _) =>
          addIfFree(res, tree.tpe)
        case Select(qualifier, _) =>
          if (free(tree.tpe)) res + tree.tpe
          else foldOver(res, tree)
        // case tree @ Assign(sel: Select, rhs) =>
        //   annotate(sel, rhs)
        case New(tp) =>
          val typCon = tp.tpe.dealias.typeConstructor
          addPart(res, typCon)
        case _ =>
          foldOver(res, tree)
      }
  }
}
