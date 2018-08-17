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
  import tpd._

  override def phaseName: String = Checker.name

  /*
  override def transformDefDef(ddef: tpd.DefDef)(implicit ctx: Context): tpd.Tree = {
    val sym = ddef.symbol
    val overrideInit = sym.allOverriddenSymbols.exists(_.hasAnnotation(defn.PartialAnnot))

    if (overrideInit ||sym.hasAnnotation(defn.PartialAnnot)) {
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
  } */

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

    val analyzer = new Analyzer

    // current class env needs special setup
    val root = Analyzer.createRootEnv

    // create a custom ObjectInfo for `this`, which implements special rules about member selection
    val env = setupConstructorEnv(root, cls, tree, analyzer)

    val res = analyzer.checkStats(tree.body, root)

    res.effects.foreach(_.report)
    env.notAssigned.foreach { sym =>
      ctx.warning(s"field ${sym.name} is not initialized", sym.pos)
    }

    tree
  }

  def setupConstructorEnv(outerEnv: Env, cls: ClassSymbol, tmpl: tpd.Template, analyzer: Analyzer, static: Boolean = false)(implicit ctx: Context) = {
    val env = outerEnv.newEnv()
    val accessors = cls.paramAccessors.filterNot(x => x.isSetter)

    for (param <- accessors)
      env.add(param, SymInfo(assigned = true, state = Analyzer.typeState(param.info)))

    analyzer.indexStats(tmpl.body, env)

    val thisInfo =  Analyzer.objectInfo(env.id, cls.isEffectivelyFinal || static)
    outerEnv.add(cls, SymInfo(state = State.Partial, latentInfo = thisInfo))

    env
  }

}
