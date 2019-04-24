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
import Decorators._
import DenotTransformers._
import config.Printers.init.{ println => debug }
import Constants.Constant
import collection.mutable

class Analyzer(cls: ClassSymbol) { analyzer =>
  import tpd._

  def checkApply(tree: Tree, fun: Tree, argss: List[List[Tree]])(implicit ctx: Context): Res =
    argss.flatten.foldRight(apply(fun)) { (arg, res) => apply(arg) + res }

  def checkSelect(tree: Select)(implicit ctx: Context): Res = apply(tree.qualifier)

  def checkClosure(sym: Symbol, tree: Tree)(implicit ctx: Context): Res =
    Res(latent = summary(sym))

  def checkIf(tree: If)(implicit ctx: Context): Res =
    apply(tree.cond) + apply(tree.thenp) + apply(tree.elsep)

  def checkValDef(vdef: ValDef)(implicit ctx: Context): Res = {
    val res = apply(vdef.rhs)
    if (vdef.symbol.is(Lazy)) {
      summary(vdef.symbol) = res.actual ++ res.latent
      Res()
    }
    else {
      summary(vdef.symbol) = res.latent
      Res(res.actual)
    }
  }

  def checkBlock(tree: Block)(implicit ctx: Context): Res = {
    // TODO: be lazy
    tree.stats.foreach {
      case ddef: DefDef =>
        val res = apply(ddef.rhs)(ctx.withOwner(ddef.symbol))
        // TODO: handle latent effects of method return?
        summary(ddef.symbol) = res._1 ++ res._2
      case _ =>
        // TODO: handle local class
    }

    val res1 = tree.stats.foldRight(Res()) { (stat, res) => res | apply(stat) }
    val res2 = apply(tree.expr)

    // remove local keys -- including ValDef, DefDef
    tree.stats.foreach {
      case ddef: DefTree =>
        summary -= ddef.symbol
      case _ =>
    }

    res1 | res2
  }

  // TODO: maybe remember `this.field_=` as well?
  def checkAssign(lhs: Select, rhs: Tree)(implicit ctx: Context): Res =
    apply(lhs.qualifier) + apply(rhs)

  def checkLocalAssign(lhs: Ident, rhs: Tree)(implicit ctx: Context): Res =
    apply(rhs).actualize

  /** Check a parent call */
  def checkInit(tp: Type, init: Symbol, argss: List[List[Tree]])(implicit ctx: Context): Res = ???

  def checkParents(cls: ClassSymbol, parents: List[Tree])(implicit ctx: Context): Res = ???

  def checkNew(tree: Tree, tref: TypeRef, init: Symbol, argss: List[List[Tree]])(implicit ctx: Context): Res = ???

  // TODO: handle outer classes
  def checkSuperSelect(tree: Select, supert: Super)(implicit ctx: Context): Res = Res(Set(tree.tpe))

  // TODO: handle outer classes
  def checkThisSelect(tree: Select, thist: This)(implicit ctx: Context): Res = Res(Set(tree.tpe))

  // TODO: handle outer classes
  def checkThis(tree: This): Res = Res(Set(tree.tpe))

  // TODO: handle local class reference
  def checkRef(tp: Type)(implicit ctx: Context): Res = tp.dealias match {
    case tp : TermRef if tp.symbol.is(Module) && ctx.owner.isContainedIn(tp.symbol.moduleClass) =>
      // self reference by name: object O { ... O.xxx }
      checkRef(ThisType.raw(tp.symbol.moduleClass.typeRef))
    case tp @ TermRef(NoPrefix, _) =>
      // TODO: local definition in outer class
      // only propagate local effects
      if (summary.contains(tp.symbol)) Res(summary(tp.symbol)) else Res()
    case tp @ TermRef(ThisType(tref), _) =>
      val cls = tref.symbol
      // TODO: handle outer this
      // ThisType used outside of class scope, can happen for objects
      // see tests/pos/t2712-7.scala
      if (cls.is(Package) || (cls.is(Flags.Module) && !ctx.owner.isContainedIn(cls)))
        Res()
      else Res(Set(tp))
    case _ =>
      Res()
  }

  object NewEx {
    def extract(tp: Type)(implicit ctx: Context): TypeRef = tp.dealias match {
      case tref: TypeRef => tref
      case AppliedType(tref: TypeRef, targs) => tref
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

  private def apply(tree: Tree)(implicit ctx: Context): Res = tree match {
    case vdef: ValDef if !vdef.rhs.isEmpty =>
      checkValDef(vdef)
    case _: DefTree =>
      Res()
    case Closure(_, meth, _) =>
      checkClosure(meth.symbol, tree)
    case tree: Ident if tree.symbol.isTerm =>
      checkRef(tree.tpe)
    case tree: This =>
      checkThis(tree)
    case tree @ Select(supert: Super, _) =>
      checkSuperSelect(tree, supert)
    case tree @ Select(thist: This, _) =>
      checkThisSelect(tree, thist)
    case tree: Select if tree.symbol.isTerm =>
      checkSelect(tree)
    case tree: If =>
      checkIf(tree)
    case tree @ NewEx(tref, init, argss) => // must before Apply
      checkNew(tree, tref, init, argss)
    case tree: Apply =>
      val (fn, targs, vargss) = decomposeCall(tree)
      checkApply(tree, fn, vargss)
    case tree @ Assign(sel: Select, rhs) =>
      checkAssign(sel, rhs)
    case tree @ Assign(id: Ident, rhs) =>
      checkLocalAssign(id, rhs)
    case tree: Block =>
      checkBlock(tree)
    case Typed(expr, tpt) =>
      apply(expr)
    case Inlined(call, bindings, expansion) =>
      checkBlock(Block(bindings, expansion))
    case _ =>
      Res()
  }

  def check(tree: TypeDef)(implicit ctx: Context) = {
    val tmpl = tree.rhs.asInstanceOf[Template]

    debug("*************************************")
    debug("checking " + cls.show)

    // TODO: be lazy
    tmpl.body.foreach {
      case ddef: DefDef if !ddef.symbol.is(Deferred) =>
        val res = apply(ddef.rhs)(ctx.withOwner(ddef.symbol))
        // TODO: handle latent effects of method return?
        summary(ddef.symbol) = res._1 ++ res._2
      case _ =>
        // TODO: handle inner class
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


    // check parent constructor code according to linearization ordering
    debug("base classes:" + tree.tpe.baseClasses.mkString(", "))
    tree.tpe.baseClasses.foreach { cls =>
      // TODO: remember which constructor is called for each class
      if (cls.primaryConstructor.hasAnnotation(defn.BodyAnnot))
        debug("body of " + cls + ":" + Inliner.bodyToInline(cls.primaryConstructor).show)
    }

    val res = tmpl.body.foldRight(Res()) { (stat, res) => res | apply(stat) }
    summary(tmpl.constr.symbol) = res.actual

    debug(showSummary)

    debug("*************************************")
  }

  def showSummary(implicit ctx: Context): String =
    summary.map { (k, v) =>
      k.show + " -> " + v.map(_.show).mkString("{", ",", "}")
    }.mkString("\n")

  // ==================== data ====================

  /** The summary of effects for class member
   *
   *   - method     : calling effects
   *   - lazy val   : access effects
   *   - val        : usage effects (take access as usage)
   */
  private val summary = mutable.Map[Symbol, Set[Type]]()
}