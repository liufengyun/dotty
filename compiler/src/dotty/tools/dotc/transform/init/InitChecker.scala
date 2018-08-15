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
import util.Positions._
import config.Printers.init.{ println => debug }
import Constants.Constant
import collection.mutable

object Checker {
  val name = "initChecker"

  def isPartial(sym: Symbol)(implicit ctx: Context) = sym.info.hasAnnotation(defn.PartialAnnot)

  def isFilled(sym: Symbol)(implicit ctx: Context) = sym.info.hasAnnotation(defn.FilledAnnot)

  def paramState(sym: Symbol)(implicit ctx: Context) =
    if (isPartial(sym)) State.Partial
    else if (isFilled(sym)) State.Filled
    else State.Full

  def isConcreteField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Deferred | Method | Local | Private)

  def isNonParamField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Method | ParamAccessor | Lazy | Deferred)

  def isField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Method | Lazy | Deferred)

  def createRootEnv: Env = {
    val heap = new Heap
    val env = new Env(-1)
    heap.addEnv(heap)
    env
  }

  def setupClassEnv(env: Env, cls: ClassSymbol)(implicit ctx: Context) = {
    val accessors = cls.paramAccessors.filterNot(x => x.isSetter)

    for (param <- accessors) env.add(param, SymInfo(assigned = true, state = paramState(sym)))

    // fields of super class
    for (
      parent <- cls.baseClasses.tail;
      decl <- parent.info.decls.toList
      if isConcreteField(decl)
    )
    env.add(param, SymInfo(assigned = true, state = paramState(sym)))

    // non-initialized fields of current class
    for (decl <- cls.info.decls.toList if isNonParamField(decl))
    env.add(param, SymInfo(assigned = false))
  }

  def setupMethodEnv(env: FreshEnv, cls: ClassSymbol, meth: Symbol, isOverriding: Boolean)(implicit ctx: Context) = {
    val accessors = cls.paramAccessors.filterNot(x => x.isSetter)

    var noninit = Set[Symbol]()    // definitions that are not initialized
    var partial = Set[Symbol]()    // definitions that are partial initialized

    // partial fields of current class
    for (param <- accessors if isPartial(param)) partial += param

    // partial fields of super class
    for (
      parent <- cls.baseClasses.tail;
      decl <- parent.info.decls.toList
      if isConcreteField(decl) && isPartial(decl)
    )
    partial += decl

    // non-initialized fields of current class
    if (cls.is(Trait))
      for (decl <- cls.info.decls.toList if isField(decl))
      noninit += decl
    else if (isOverriding)
      for (decl <- cls.info.decls.toList if isNonParamField(decl))
      noninit += decl

    env.setNonInit(noninit)
    env.setPartialSyms(partial)
    env.setLocals(noninit ++ partial)
  }
}

/** This transform checks initialization is safe based on data-flow analysis
 *
 *  - Partial
 *  - Filled
 *  - Full
 *
 *  1. A _full_ object is fully initialized.
 *  2. All fields of a _filled_ object are assigned, but the fields may refer to non-full objects.
 *  3. A _partial_ object may have unassigned fields.
 *
 *  TODO:
 *   - check default arguments of init methods
 *   - selection on ParamAccessors of partial value is fine if the param is not partial
 *   - handle tailrec calls during initialization (which captures `this`)
 */
class Checker extends MiniPhase with IdentityDenotTransformer { thisPhase =>
  import tpd._, InitChecker._

  override def phaseName: String = InitChecker.name

  override def transformDefDef(ddef: tpd.DefDef)(implicit ctx: Context): tpd.Tree = {
    val sym = ddef.symbol
    val overrideInit = sym.allOverriddenSymbols.exists(_.hasAnnotation(defn.InitAnnot))

    if (overrideInit ||sym.hasAnnotation(defn.InitAnnot)) {
      val cls = sym.owner.asClass
      val root = createRootEnv

      val classEnv = setupMethodEnv(root.newEnv, sym.owner.asClass, sym, isOverriding = overrideInit)
      val thisInfo = new ObjectEnv(classEnv.id)

      root.setPartialSyms(Set(cls))
      root.setLatentSyms(Map(cls -> thisInfo))

      val checker = new DataFlowChecker

      val res = checker.apply(ddef.rhs, classEnv)
      res.effects.foreach(_.report)
      if (res.effects.nonEmpty) ctx.warning(s"init $sym may cause initialization problems", ddef.pos)
    }

    ddef
  }

  override def transformTemplate(tree: Template)(implicit ctx: Context): Tree = {
    val cls = ctx.owner.asClass
    val self = cls.thisType

    if (cls.hasAnnotation(defn.UncheckedAnnot)) return tree

    def lateInitMsg(sym: Symbol) =
      s"""|Initialization too late: $sym may be used during parent initialization.
          |Consider make it a class parameter."""
        .stripMargin

    for (decl <- cls.info.decls.toList if decl.is(AnyFlags, butNot = Method | Deferred)) {
      val overrideInit = decl.allOverriddenSymbols.exists(_.hasAnnotation(defn.InitAnnot))
      if (overrideInit && !decl.is(ParamAccessor | Override))
        ctx.warning(lateInitMsg(decl), decl.pos)
    }

    var membersToCheck: util.SimpleIdentityMap[Name, Type] = util.SimpleIdentityMap.Empty[Name]
    val seenClasses = new util.HashSet[Symbol](256)

    def parents(cls: Symbol) =
      cls.info.parents.map(_.classSymbol)
        .filter(_.is(AbstractOrTrait))
        .dropWhile(_.is(JavaDefined | Scala2x))

    def addDecls(cls: Symbol): Unit =
      if (!seenClasses.contains(cls)) {
        seenClasses.addEntry(cls)
        for (mbr <- cls.info.decls)
          if (mbr.isTerm && mbr.is(Deferred | Method) &&
              (mbr.hasAnnotation(defn.PartialAnnot) || mbr.hasAnnotation(defn.FilledAnnot)) &&
              !membersToCheck.contains(mbr.name))
            membersToCheck = membersToCheck.updated(mbr.name, mbr.info.asSeenFrom(self, mbr.owner))
          parents(cls).foreach(addDecls)
      }
    parents(cls).foreach(addDecls)  // no need to check methods defined in current class

    def invalidImplementMsg(sym: Symbol) =
      s"""|@scala.annotation.partial required for ${sym.show} in ${sym.owner.show}
          |Because the abstract method it implements is marked as `@partial` or `@filled`."""
        .stripMargin

    for (name <- membersToCheck.keys) {
      val tp  = membersToCheck(name)
      for {
        mbrd <- self.member(name).alternatives
        if mbrd.info.overrides(tp, matchLoosely = true)
      } {
        val mbr = mbrd.symbol
        if (mbr.owner.ne(cls) && !mbr.hasAnnotation(defn.PartialAnnot))
          ctx.warning(invalidImplementMsg(mbr), cls.pos)
      }
    }

    val checker = new DataFlowChecker

    // current class env needs special setup
    val root = createRootEnv

    // create a custom ObjectInfo for `this`, which implements special rules about member selection
    val env = setupClassEnv(root.newEnv(), cls)
    checker.indexStats(tree.body, env)
    val thisInfo =  ObjectInfo {
      (sym: Symbol, heap: Heap, pos: Position) => ???
    }

    root.add(cls, SymInfo(state = State.Partial, latentInfo = thisInfo))

    val res = checker.checkStats(tree.body, root)
    res.effects.foreach(_.report)
    env.nonInit.foreach { sym =>
      ctx.warning(s"field ${sym.name} is not initialized", sym.pos)
    }

    tree
  }
}
