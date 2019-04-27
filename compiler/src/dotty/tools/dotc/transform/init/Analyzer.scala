package dotty.tools.dotc
package transform
package init

import core._
import typer._
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
import util.SourcePosition
import config.Printers.init.{ println => debug }
import Constants.Constant
import collection.mutable

class Analyzer(cls: ClassSymbol) { analyzer =>
  import tpd._

  object NewEx {
    def extract(tp: Type)(implicit ctx: Context): TypeRef = tp.dealias match {
      case tref: TypeRef => tref
      case AppliedType(tref: TypeRef, targs) => tref
      case hktp: HKTypeLambda => extract(hktp.hkResult)
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

  object Function {
    def unapply(tree: Tree)(implicit ctx: Context): Option[Tree] = tree match {
      case Block((ddef: DefDef) :: Nil, Closure(_, meth, _)) if meth.symbol == ddef.symbol => Some(ddef.rhs)
      case _ => None
    }
  }

  /** SLS 5.1
    *
    *  Template Evaluation Consider a template `sc with mt1 with mtn { stats }`.
    *
    *  If this is the template of a trait then its mixin-evaluation consists of
    *  an evaluation of the statement sequence stats.
    *
    *  If this is not a template of a trait, then its evaluation consists of the following steps.
    *
    *  - First, the superclass constructor sc is evaluated.
    *  - Then, all base classes in the template's linearization up to the template's
    *    superclass denoted by sc are mixin-evaluated. Mixin-evaluation happens in reverse
    *    order of occurrence in the linearization.
    *  - Finally the statement sequence stats is evaluated.
    */
  def checkTemplate(curCls: ClassSymbol, body: Tree)(implicit ctx: Context): Unit = {
    if (body.isEmpty) return

    curCls.paramAccessors.foreach(sym => initialized += sym)

    val Block(sc :: stats, _) = body
    // super constructor call
    sc match {
      case tree @ NewEx(tref, init, argss) =>
        // Note: effects on outer already handled, only care about `this`
        val cls = tref.classSymbol.asClass
        checkTemplate(cls, Checker.getConstructorCode(cls))
        // TODO: check possible 2nd constructor effects
      case tree =>
        val cls = tree.tpe.classSymbol.asClass
        checkTemplate(cls, Checker.getConstructorCode(cls))
    }

    // mixin-evaluation of traits
    curCls.typeRef.baseClasses.tail.takeWhile(_ != sc.tpe.classSymbol).reverse.foreach { base =>
      base.paramAccessors.foreach(sym => initialized += sym)
      if (base.primaryConstructor.hasAnnotation(defn.BodyAnnot)) {
        val Block(stats, _) = Inliner.bodyToInline(base.primaryConstructor)
        stats.foreach(checkStat(base, _))
      }
    }

    // template body
    stats.foreach(checkStat(curCls, _))
  }

  /** The capture on `this` */
  private def capture(cls: ClassSymbol, tree: Tree)(implicit ctx: Context): Set[Type] =
    new CaptureAnalyzer.CaptureAnalysis(cls).apply(Set.empty, tree)

  /** The set of fields reachable from the set of references */
  private def fixpoint(uses: Set[Type], pos: SourcePosition)(implicit ctx: Context): Set[Symbol] = {
    def propagate(tp: Type): Set[Type] = tp match {
      case tp: TermRef =>
        val res = resolve(tp).uses.toSet
        debug(tp.symbol.show + " -> " + res.map(_.show).mkString(", "))
        res
      case tp: ThisType  =>
        ctx.error(s"Leak of ${tp.cls.name.show}.this", pos)
        Set()
      case tp: TypeRef =>
        // handle inner class
        val res = tp.symbol.uses.toSet
        debug(tp.symbol.show + " -> " + res.map(_.show).mkString(", "))
        res
      case _ =>
        Set()
    }

    def resolve(tp: TermRef): Symbol =
      tp.symbol.matchingMember(cls.typeRef).orElse(tp.symbol)

    def accumulate(uses: Set[Type], seen: Set[Type], acc: Set[Symbol]): Set[Symbol] =
      if (uses.isEmpty) acc
      else {
        val (head, tail) = uses.splitAt(1) match { case (s1, s2) => (s1.head, s2) }
        if (seen.contains(head)) accumulate(tail, seen, acc)
        else {
          debug("head = " + head)
          val seen2 = seen + head
          val acc2 = head match {
            case tmref: TermRef =>
              val sym = resolve(tmref)
              if (!sym.is(Method) && !sym.is(Lazy)) {
                debug(tmref.show + " -> " + resolve(tmref).show)
                acc + sym
              }
              else acc
            case _ => acc
          }
          val uses2 = tail ++ propagate(head) -- seen2
          accumulate(uses2, seen2, acc2)
        }
      }

    accumulate(uses, Set.empty, Set.empty)
  }

  private def checkStat(cls: ClassSymbol, tree: Tree)(implicit ctx: Context): Unit = {
    // TODO: error reporting should respect separate compilation.
    //       It does not make sense to report error in pre-compiled souce code.
    def check(tree: Tree) = {
      debug("checking " + tree.show)
      val free = capture(cls, tree)
      debug("free = " + free.map(_.show).mkString(", "))
      val effects = fixpoint(free, tree.sourcePos)
      debug("effects = " + effects.map(_.show).mkString(", "))
      debug("initialized = " + initialized.map(_.show).mkString(", "))
      val uninit = effects -- initialized
      if (uninit.nonEmpty)
        ctx.error(s"The code access uninit field(s) when instantiating ${this.cls.show}: " + uninit.map(_.termRef.show).mkString(", "), tree.sourcePos)
    }

    tree match {
      case vdef: ValDef if !vdef.rhs.isEmpty =>
        vdef.rhs match {
          case Function(body) =>
            val frees = capture(cls, body)
            frees.foreach { tp => vdef.symbol.addAnnotation(Annotation.Use(tp)) }
          case _ => check(vdef.rhs)
        }
        initialized += vdef.symbol
      case _ =>
        check(tree)
    }
  }

  private val initialized = mutable.Set[Symbol]()
}