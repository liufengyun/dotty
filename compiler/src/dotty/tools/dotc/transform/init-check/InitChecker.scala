package dotty.tools.dotc
package transform

import core._
import MegaPhase._
import Contexts.Context
import StdNames._
import Phases._
import ast._
import Trees._
import Flags._
import SymUtils._
import Symbols._
import SymDenotations._
import Types._
import Decorators._
import DenotTransformers._
import util.Positions._
import config.Printers.init.{ println => debug }
import Constants.Constant
import collection.mutable

object InitChecker {
  val name = "initChecker"
}

import DataFlowChecker._

/** This transform checks initialization is safe based on data-flow analysis
 *   - `init` methods cannot be overriden
 *   - partial values cannot be used as full values
 *   - a partial value can only be assigned to uninitialized field of a partial value
 *   - selection on a partial value is an error, unless the accessec field is initialized (super fields are not initialized)
 *
 *  Partial values are defined as follows:
 *   - params with the type `T @partial`
 *   - `this` in constructor unless it's known to be fully initialized
 *   - `new C(args)`, if any argument is partial
 *   - `val x = rhs` where the right-hand-side is partial
 *   - `x => body` where the right-hand-side access uninitialized fields
 *
 *  TODO:
 *   - parent call abstract methods during initialization
 *      - scala/tools/nsc/backend/jvm/BackendInterface.scala:722
 *      - scala/tools/nsc/backend/jvm/BCodeBodyBuilder.scala:1451
 *      - scala/tools/nsc/backend/jvm/BackendInterface.scala:727
 *      - compiler/src/dotty/tools/dotc/config/Properties.scala:23
 *      - compiler/src/dotty/tools/dotc/config/Properties.scala:69
 *      - compiler/src/dotty/tools/dotc/core/Denotations.scala:1162
 *      - compiler/src/dotty/tools/io/AbstractFile.scala:97
 *   - child call parent method during initialization
 *      - compiler/src/dotty/tools/dotc/config/ScalaSettings.scala:16
 *      - compiler/src/dotty/tools/dotc/ast/DesugarEnums.scala:19
 *      - compiler/src/dotty/tools/dotc/core/Contexts.scala:573
 *      - compiler/src/dotty/tools/dotc/core/StdNames.scala:63
 *      - compiler/src/dotty/tools/dotc/core/unpickleScala2/Scala2Unpickler.scala:236
 *      - compiler/src/dotty/tools/dotc/interactive/InteractiveDriver.scala:34
 *      - compiler/src/dotty/tools/dotc/parsing/JavaTokens.scala:18
 *      - compiler/src/dotty/tools/dotc/typer/Applications.scala:546
 *   - select field of parent
 *      - compiler/src/dotty/tools/dotc/ast/Desugar.scala:82
 *      - compiler/src/dotty/tools/dotc/core/Contexts.scala:573
 *      - compiler/src/dotty/tools/dotc/core/Comments.scala:120
 *      - compiler/src/dotty/tools/dotc/core/tasty/TreeBuffer.scala:14
 *   - `this` escape as full value
 *      - compiler/src/dotty/tools/dotc/Run.scala:61
 *      - compiler/src/dotty/tools/dotc/core/Contexts.scala:552
 *      - compiler/src/dotty/tools/dotc/core/Types.scala:2353
 *      - compiler/src/dotty/tools/dotc/core/Types.scala:3054
 *      - compiler/src/dotty/tools/dotc/core/Types.scala:3073
 *      - compiler/src/dotty/tools/dotc/core/tasty/TastyPickler.scala:73
 *      - compiler/src/dotty/tools/dotc/typer/RefChecks.scala:851
 *   - `this` escape in a partial closure
 *      - compiler/src/dotty/tools/dotc/core/Definitions.scala:855
 *      - compiler/src/dotty/tools/dotc/transform/LambdaLift.scala:354
 *      - compiler/src/dotty/tools/dotc/transform/MegaPhase.scala:402
 *   - init methods not final or private
 *      - compiler/src/dotty/tools/dotc/ast/Positioned.scala:118
 *      - compiler/src/dotty/tools/dotc/ast/Positioned.scala:54
 *      - compiler/src/dotty/tools/dotc/parsing/CharArrayReader.scala:10
 *      - compiler/src/dotty/tools/dotc/parsing/JavaScanners.scala:534
 *   - `this` escape in val overriding method
 *      - compiler/src/dotty/tools/dotc/core/Contexts.scala:538
 *   - create instance of nested class
 *      - compiler/src/dotty/tools/dotc/core/NameKinds.scala:68
 *   - fix me
 *      - compiler/src/dotty/tools/dotc/core/NameKinds.scala:88
 *      - compiler/src/dotty/tools/dotc/core/SymDenotations.scala:1355
 *      - compiler/src/dotty/tools/dotc/reporting/diagnostic/messages.scala:1342 default methods
 */
class InitChecker extends MiniPhase with IdentityDenotTransformer { thisPhase =>
  import tpd._

  override def phaseName: String = InitChecker.name

  override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context): tpd.Tree = {
    if (tree.symbol.hasAnnotation(defn.InitAnnot) && tree.symbol.is(Override))
      ctx.warning("Initialization methods cannot be overriden", tree.pos)

    if (tree.symbol.hasAnnotation(defn.InitAnnot) && tree.symbol.is(Deferred))
      ctx.warning("Initialization methods cannot be abstract", tree.pos)

    tree
  }

  override def transformTemplate(tree: Template)(implicit ctx: Context): Tree = {
    val cls = ctx.owner.asClass

    if (cls.hasAnnotation(defn.PartialAnnot)) return tree

    val accessors = cls.paramAccessors.filterNot(x => x.isSetter)

    var noninit = Set[Symbol]()    // definitions that are not initialized
    var partial = Set[Symbol]()    // definitions that are partial initialized

    def isPartial(sym: Symbol) = sym.info.hasAnnotation(defn.PartialAnnot)

    def isConcreteField(sym: Symbol) =
      sym.isTerm && sym.is(AnyFlags, butNot = Deferred | Method | Local | Private)

    def isNonParamField(sym: Symbol) =
      sym.isTerm && sym.is(AnyFlags, butNot = Method | ParamAccessor | Lazy | Deferred)

    // partial fields of current class
    for (
      param <- accessors
      if isPartial(param)
    )
    partial += param

    // partial fields of super class
    for (
      parent <- cls.baseClasses.tail;
      decl <- parent.info.decls.toList
      if isConcreteField(decl) && isPartial(decl)
    )
    partial += decl

    // add current this
    partial += cls

    // non-initialized fields of current class
    for (
      decl <- cls.info.decls.toList
      if isNonParamField(decl)
    )
    noninit += decl

    val checker = new DataFlowChecker(cls, noninit, partial)

    checker(tree).foreach(_.report)
    checker.noninit.foreach { sym =>
      ctx.warning(s"field ${sym.name} is not initialized", sym.pos)
    }

    tree
  }
}

object DataFlowChecker {
  sealed trait Effect {
    def report(implicit ctx: Context): Unit = this match {
      case Member(sym, obj, pos)    =>
        ctx.warning(s"Select $sym on partial value", pos)
      case Uninit(sym, pos)         =>
        ctx.warning(s"Reference to uninitialized value `${sym.name}`", pos)
      case OverrideRisk(sym, pos)     =>
        if (sym.is(Deferred))
          ctx.warning(s"`@scala.annotation.partial` is recommended for abstract $sym for safe initialization", sym.pos)
        else
          ctx.warning(s"`private` is recommended for $sym to avoid overriding", sym.pos)
        ctx.warning(s"Reference to $sym which could be overriden", pos)
      case Call(sym, effects, pos)  =>
        ctx.warning(s"The call to `${sym.name}` causes initialization problem", pos)
        effects.foreach(_.report)
      case Force(sym, effects, pos) =>
        ctx.warning(s"Forcing lazy val `${sym.name}` causes initialization problem", pos)
        effects.foreach(_.report)
      case Argument(sym, arg)       =>
        ctx.warning(s"Use partial value as a full value", arg.pos)
      case CrossAssign(lhs, rhs)    =>
        ctx.warning(s"Assign partial value to a non-partial value", rhs.pos)
      case PartialNew(prefix, cls, pos)  =>
        ctx.warning(s"Cannot create $cls because the prefix `${prefix.name.show}` is partial", pos)
      case Instantiate(cls, effs, pos)  =>
        ctx.warning(s"Create instance results in initialization errors", pos)
        effs.foreach(_.report)
      case UseAbstractVal(sym, pos)  =>
         ctx.warning(s"abstract $sym cannot be used during initialization. Consider change it to a method.", pos)
    }
  }
  case class Uninit(sym: Symbol, pos: Position) extends Effect                         // usage of uninitialized values
  case class OverrideRisk(sym: Symbol, pos: Position) extends Effect                   // calling methods that are not override-free
  case class Call(sym: Symbol, effects: Seq[Effect], pos: Position) extends Effect     // calling method results in error
  case class Force(sym: Symbol, effects: Seq[Effect], pos: Position) extends Effect    // force lazy val results in error
  case class Argument(fun: Symbol, arg: tpd.Tree) extends Effect                       // use of partial values as full values
  case class Member(sym: Symbol, obj: tpd.Tree, pos: Position) extends Effect          // select members of partial values
  case class CrossAssign(lhs: tpd.Tree, rhs: tpd.Tree) extends Effect                  // assign a partial values to non-partial value
  case class PartialNew(prefix: Symbol, cls: Symbol, pos: Position) extends Effect     // create new inner class instance while outer is partial
  case class Instantiate(cls: Symbol, effs: Seq[Effect], pos: Position) extends Effect // create new instance of in-scope inner class results in error
  case class UseAbstractVal(sym: Symbol, pos: Position) extends Effect                 // use abstract val during initialization, see override6.scala

  trait Effects {
    def effects: Vector[Effect]
  }

  class LazyEffects(effs: => Vector[Effect]) extends Effects {
    lazy val effects = effs
  }

  class MethodEffects(effs: => Vector[Effect]) extends Effects {
    def effects = effs
  }
}

class DataFlowChecker(
  cls: Symbol,
  var noninit: Set[Symbol],
  var partialSyms: Set[Symbol],
  var defns: Map[Symbol, tpd.Tree] = Map(),
  var lazyForced: Set[Symbol] = Set(),
  var methChecking: Set[Symbol] = Set(),
  var partialValues: util.SimpleIdentitySet[tpd.Tree] = util.SimpleIdentitySet.empty
  ) extends tpd.TreeAccumulator[Vector[Effect]] {


  import tpd._

  def diagnose(implicit ctx: Context) = {
    debug(s"------------ $cls ------------->")
    debug("not initialized: " + noninit)
    debug("partial initialized: " + partialSyms)
    debug("lazy forced: " + lazyForced)
    debug("definitions map: " + defns.keys)
    debug(s"<--------------------------------")
  }

  def show(implicit ctx: Context) = {
    println(s"------------ $cls ------------->")
    println("not initialized: " + noninit)
    println("partial initialized: " + partialSyms)
    println("lazy forced: " + lazyForced)
    println("definitions map: " + defns.keys)
    println(s"<--------------------------------")
  }

  def checkOverride(sym: Symbol, pos: Position)(implicit ctx: Context): Vector[Effect] =
    if (sym.hasAnnotation(defn.PartialAnnot) || sym.owner.ne(cls) || sym.is(Final | Private) || cls.is(Final))
      Vector.empty
    else
      Vector(OverrideRisk(sym, pos))

  def checkUsage(sym: Symbol, pos: Position)(implicit ctx: Context): Vector[Effect] =
    if (noninit.contains(sym)) Vector(Uninit(sym, pos))
    else Vector.empty

  def checkForce(sym: Symbol, pos: Position)(implicit ctx: Context): Vector[Effect] =
    if (!sym.is(Lazy) || lazyForced.contains(sym)) Vector.empty
    else {
      lazyForced += sym
      val lazyValEffs = effects(sym)
      if (lazyValEffs.size > 0) Vector(Force(sym, lazyValEffs, pos))
      else Vector.empty
    }

  def checkCall(sym: Symbol, pos: Position)(implicit ctx: Context): Vector[Effect] = {
    debug("checking call " + sym)
    if (!sym.is(Method) || sym.is(Label)) Vector.empty
    else if (methChecking.contains(sym)) {
      debug("recursive call found during initialization")
      Vector.empty
    }
    else {
      methChecking += sym
      val methEffs = effects(sym) ++ checkOverride(sym, pos)
      methChecking -= sym
      if (methEffs.size > 0) Vector(Call(sym, methEffs, pos)) else Vector.empty
    }
  }

  def checkNew(tree: tpd.Tree, tpt: tpd.Tree)(implicit ctx: Context): Vector[Effect] = {
    def check(prefix: Type, clazz: Symbol): Vector[Effect] = prefix match {
      case prefix : TermRef if isPartial(prefix.symbol) =>
        Vector(PartialNew(prefix.symbol, tpt.symbol, tree.pos))
      case ThisType(tref) if isPartial(tref.symbol) =>
        if (clazz.exists && tref.symbol == cls && clazz.owner == cls) { // if the class is nested in scope
          val effs = effects(clazz)
          if (effs.size > 0) Vector(Instantiate(tref.symbol, effs, tree.pos)) else Vector.empty
        }
        else Vector(PartialNew(tref.symbol, tpt.symbol, tree.pos))
      case _ =>
        Vector.empty
    }

    def extract(tp: Type): (Type, Symbol) = tp.dealias match {
      case tref: TypeRef => (tref.prefix, tref.symbol)
      case AppliedType(tref: TypeRef, targs) => extract(tref)
    }

    val (prefix, clazz) = extract(tpt.tpe)
    check(prefix, clazz)
  }

  def checkApply(tree: tpd.Tree, fun: tpd.Tree, args: List[tpd.Tree])(implicit ctx: Context): Vector[Effect] = {
    val paramInfos = fun.tpe.widen.asInstanceOf[MethodType].paramInfos
    def isParamPartial(index: Int) = paramInfos(index).hasAnnotation(defn.PartialAnnot)

    var argEffs = Vector.empty[Effect]

    args.zipWithIndex.foreach { case (arg, index) =>
      argEffs = argEffs ++ apply(arg) ++ {
        if (!isPartial(arg)) Vector.empty
        else if (isParamPartial(index)) {
          partialValues -= arg
          partialValues += tree
          Vector.empty
        }
        else {
          partialValues -= arg
          Vector(Argument(fun.symbol, arg))
        }
      }
    }

    argEffs
  }

  def checkSelect(tree: tpd.Select)(implicit ctx: Context): Vector[Effect] =
    if (!isPartial(tree.qualifier)) Vector.empty
    else {
      partialValues -= tree.qualifier
      Vector(Member(tree.symbol, tree.qualifier, tree.pos))
    }

  /** return the top-level local term within `cls` refered by `tp`, NoType otherwise.
   *
   *  There are following cases:
   *   - select on this: `C.this.x`
   *   - select on super: `C.super[Q].x`
   *   - local ident: `x`
   *   - select on self: `self.x` (TODO)
   */
  def localRef(tp: Type)(implicit ctx: Context): Type = tp match {
    case TermRef(ThisType(tref), _) if tref.symbol.isContainedIn(cls) => tp
    case TermRef(SuperType(ThisType(tref), _), _) if tref.symbol.isContainedIn(cls) => tp
    case tmref @ TermRef(NoPrefix, _) if tmref.symbol.isContainedIn(cls) => tmref
    case TermRef(tp: TermRef, _) => localRef(tp)
    case _ => NoType
  }

  /** Does the TermRef refer to a symbol defined within `cls`?
   *
   *  precondition: localRef(tp) != NoType
   */
  def isLexicalRef(tp: TermRef)(implicit ctx: Context): Boolean =
    tp.symbol.isContainedIn(cls)

  /** Is the TermRef a reference to safe member defined in the parent of `cls`?
   *
   *  A member access is safe in the following cases:
   *  - a non-lazy, non-deferred field where the primary constructor takes no partial values
   *  - a method marked as `@init`
   */
  def isSafeParentAccess(tp: TermRef)(implicit ctx: Context): Boolean =
    tp.symbol.owner.isClass && cls.isSubClass(tp.symbol.owner) &&
      (
        tp.symbol.is(AnyFlags, butNot = Method | Lazy | Deferred) && !hasPartialParam(tp.symbol.owner) ||
        tp.symbol.hasAnnotation(defn.InitAnnot)
      )

  def hasPartialParam(clazz: Symbol)(implicit ctx: Context): Boolean =
    cls.asClass.paramAccessors.exists(_.hasAnnotation(defn.PartialAnnot))

  def checkTermRef(tree: tpd.Tree)(implicit ctx: Context): Vector[Effect] = {
    val ref: TermRef = localRef(tree.tpe) match {
      case NoType         => return Vector.empty
      case tmref: TermRef => tmref
    }

    if (isPartial(ref.symbol)) partialValues += tree

    checkUsage(ref.symbol, tree.pos) ++ {
      if (isLexicalRef(ref)) {
        if (ref.symbol.is(Lazy)) checkForce(ref.symbol, tree.pos)
        else if (ref.symbol.is(Method)) checkCall(ref.symbol, tree.pos)
        else if (ref.symbol.is(Deferred) && ref.symbol.owner == cls)
          Vector(UseAbstractVal(ref.symbol, tree.pos))
        else Vector.empty
      }
      else if (isPartial(ref.prefix) && !isSafeParentAccess(ref))
        Vector(Member(ref.symbol, tree, tree.pos))
      else
        Vector.empty
    }
  }

  def effects(sym: Symbol)(implicit ctx: Context): Vector[Effect] = {
    val tree = defns(sym)
    apply(tree)
  }

  def isPartial(tp: Type)(implicit ctx: Context): Boolean = tp match {
    case tmref: TermRef             => isPartial(tmref.symbol)
    case ThisType(tref)             => isPartial(tref.symbol)
    case SuperType(thistp, _)       => isPartial(thistp)        // super is partial if `thistp` is partial
    case _                          => false
  }

  def isPartial(sym: Symbol)(implicit ctx: Context) = partialSyms.contains(sym)
  def isPartial(tree: Tree)(implicit ctx: Context) = partialValues.contains(tree)

  def isClosurePartial(sym: Symbol)(implicit ctx: Context): Boolean = {
    debug("checking closure: " + sym)
    val tree = defns(sym)
    val checker = newChecker
    val effs = checker.apply(defns(sym))
    debug("effects of closure: " + effs)
    effs.size > 0
  }

  // partialSyms.size == 1 : no partial fields
  def thisInitialized: Boolean = noninit.isEmpty && partialSyms.size == 1

  def newChecker =
    new DataFlowChecker(cls, noninit, partialSyms, defns, lazyForced, methChecking, partialValues)

  def apply(effs: Vector[Effect], tree: Tree)(implicit ctx: Context) = tree match {
    case tmpl: Template =>
      val stats = tmpl.body.filter {
        case vdef : ValDef  =>
          !vdef.symbol.hasAnnotation(defn.ScalaStaticAnnot)
        case stat =>
          true
      }
      effs ++ apply(Block(stats, tpd.unitLiteral))
    case vdef : ValDef if !vdef.symbol.is(Lazy) =>
      val effects = apply(vdef.rhs)

      if (!tpd.isWildcardArg(vdef.rhs) && !vdef.rhs.isEmpty) noninit -= vdef.symbol  // take `_` as uninitialized, otherwise it's initialized

      if (partialValues.contains(vdef.rhs)) {
        partialValues -= vdef.rhs

        if (noninit.isEmpty && partialSyms.size == 1 && partialSyms.contains(cls)) // fully initialized
          partialSyms = Set.empty
        else
          partialSyms += vdef.symbol
      }
      effs ++ effects
    case _: DefTree =>  // ignore other definitions
      effs
    case Closure(_, meth, _) =>
      if (isClosurePartial(meth.symbol)) partialValues += tree
      effs
    case tree: Ident if tree.symbol.isTerm =>
      effs ++ checkTermRef(tree)
    case tree @ Select(prefix @ (This(_) | Super(_, _)), _) if tree.symbol.isTerm =>
      effs ++ checkTermRef(tree)
    case tree @ New(tpt) =>
      effs ++ checkNew(tree, tpt)
    case tree @ Select(prefix, _) if tree.symbol.isTerm =>
      val prefixEffs = apply(prefix)
      effs ++ prefixEffs ++ checkSelect(tree)
    case tree @ This(_) =>
      if (isPartial(tree.symbol) && !thisInitialized) partialValues += tree
      effs
    case tree @ Super(qual, mix) =>
      if (isPartial(qual.symbol) && !thisInitialized) partialValues += tree
      effs
    case tree @ If(cond, thenp, elsep) =>
      val condEffs = this(cond)
      val thenChecker = newChecker
      val elseChecker = newChecker
      val thenEffs = thenChecker(thenp)
      val elseEffs = elseChecker(elsep)

      debug("partial before if: " + partialSyms)
      debug("partial of then: " + thenChecker.partialSyms)
      debug("partial of else: " + elseChecker.partialSyms)

      noninit = thenChecker.noninit ++ elseChecker.noninit
      lazyForced = thenChecker.lazyForced ++ elseChecker.lazyForced
      partialSyms = thenChecker.partialSyms ++ elseChecker.partialSyms

      debug("partial after if: " + partialSyms)

      if (isPartial(thenp) || isPartial(elsep)) {
        partialValues -= thenp
        partialValues -= elsep
        partialValues += tree
      }

      effs ++ condEffs ++ thenEffs ++ elseEffs
    case tree @ Apply(fun, args) =>
      val funEffs = apply(fun)
      effs ++ funEffs ++ checkApply(tree, fun, args)
    case tree @ Assign(lhs @ (Ident(_) | Select(This(_), _)), rhs) =>
      effs ++ apply(rhs) ++ {
        if (!isPartial(rhs) || isPartial(lhs.symbol) || noninit.contains(lhs.symbol)) {
          noninit -= lhs.symbol
          if (!isPartial(rhs)) partialSyms -= lhs.symbol
          else {
            partialValues -= rhs
            partialSyms += lhs.symbol
          }
          Vector.empty
        }
        else
          Vector(CrossAssign(lhs, rhs))
      }
    case tree @ Assign(lhs @ Select(prefix, _), rhs) =>
      effs ++ apply(prefix) ++ apply(rhs) ++ {
        if (!isPartial(rhs) || isPartial(prefix))
          Vector.empty
        else
          Vector(CrossAssign(lhs, rhs))
      }
    case tree @ Block(stats, expr) =>
      val meths = stats.collect {
        case ddef: DefDef if ddef.symbol.is(AnyFlags, butNot = Accessor) =>
          ddef.symbol -> ddef.rhs
        case vdef: ValDef if vdef.symbol.is(Lazy)  =>
          vdef.symbol -> vdef.rhs
        case tdef: TypeDef if tdef.isClassDef  =>
          tdef.symbol -> tdef.rhs
      }
      debug("local methods: " + meths.map(_._1))
      defns ++= meths
      val res = foldOver(effs, tree)
      defns --= meths.map(_._1)

      if (partialValues.contains(expr)) {
        partialValues -= expr
        partialValues += tree
      }

      effs ++ res
    case _ =>
      foldOver(effs, tree)
  }

  def apply(tree: Tree)(implicit ctx: Context): Vector[Effect] = {
    diagnose
    debug("checking " + tree.show)
    apply(Vector.empty, tree)
  }
}