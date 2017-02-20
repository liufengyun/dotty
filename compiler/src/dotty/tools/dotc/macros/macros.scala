package dotty.tools.dotc

import core._
import Contexts.Context
import Symbols._
import Types._
import Decorators._
import ast._
import util._
import StdNames._
import typer.ErrorReporting._
import reporting.diagnostic._
import config.Printers.{macros => debug}
import dotty.tools.dotc.typer.ProtoTypes.ApplyingProto
import typer.{ForceDegree, Inferencing, Typer}

package object macros {
  import untpd._

  private class Proxy(clazz: Class[_], module: AnyRef) {
    def apply(name: String, params: Object*) = {
      val method = clazz.getDeclaredMethods().find(_.getName == name).get
      method.setAccessible(true)
      method.invoke(module, params: _*)
    }
  }

  private def forObject(qual: String)(implicit ctx: Context) = {
    val clazz = ctx.classloader.loadClass(qual + "$")
    val module = clazz.getField(str.MODULE_INSTANCE_FIELD.toString).get(null)
    new Proxy(clazz, module)
  }

  /** Whether an Apply tree is quasiquote ?
   *  @param symbol the symbol of the function in the Apply tree
   *  @param tree   the Apply tree
   */
  def isQuasiquote(symbol: Symbol)(implicit ctx: Context): Boolean =
    (symbol.isContainedIn(defn.q) || symbol.isContainedIn(defn.t)) &&
      (symbol.name == nme.apply || symbol.name == nme.unapply)

  /** Expand a quasiquote tree */
  def expandQuasiquote(tree: Tree, isTerm: Boolean)(implicit ctx: Context): Tree = {
    forObject("scala.gestalt.dotty.Expander").apply("expandQuasiquote", tree, Boolean.box(isTerm), ctx).asInstanceOf[Tree]
  }

  /** Expand annotation macros */
  def expandAnnotMacro(mdef: DefTree)(implicit ctx: Context): Tree = {
    if (
      !ctx.macrosEnabled ||
      !mdef.isInstanceOf[MemberDef] ||
      !macros.hasAnnotMacros(mdef.asInstanceOf[MemberDef])
    ) return mdef

    val tree = forObject("scala.gestalt.dotty.Expander").apply("expandAnnotMacro", mdef, ctx).asInstanceOf[Tree]
    tree match {
      case blk : Block =>   // introducing of same level symbols
        if (blk.stats.exists(!_.isInstanceOf[MemberDef]) || blk.expr != EmptyTree) {
          val errorMsg = "a definition can only expand to a list of definition. Actual:\n\n" + blk.show
          errorTree(mdef, new NoExplanation(errorMsg))
        }
        else {
          debug.println(i"macro expansion: $mdef expands to $blk")
          Thicket(blk.stats)
        }
      case _ => tree
    }
  }

  /** Does the given definition have annotation macros? */
  def hasAnnotMacros(mdef: MemberDef)(implicit ctx: Context): Boolean = {
    mdef.mods.annotations.filter(isAnnotMacro).headOption.nonEmpty
  }

  /** Is the given annotation an annotation macro? */
  def isAnnotMacro(ann: untpd.Tree)(implicit ctx: Context): Boolean = {
    import StdNames._

    val symbol = ctx.typer.typedAheadAnnotation(ann)
    if (!symbol.exists) return false

    val annMethod = symbol.info.decl(nme.apply)
    val annImplMethod = symbol.owner.info
      .decl((symbol.name + Transform.INLINE_SUFFIX).toTermName)
      .info
      .decl(nme.apply)

    symbol.typeRef <:< defn.StaticAnnotationType && annMethod.exists && annImplMethod.exists
  }

  /** Whether the given symbol is a def macro? */
  @inline
  def isDefMacro(symbol: Symbol)(implicit ctx: Context): Boolean =
    symbol.is(Flags.Macro) && !symbol.owner.is(Flags.Scala2x)

  /** Expand def macros */
  def expandDefMacro(tree: tpd.Tree, pt: Type, typer: Typer)(implicit ctx: Context): tpd.Tree = {
    def isMacroApplyEnd: Boolean =
      (tree.isInstanceOf[tpd.Apply] || tree.isInstanceOf[tpd.TypeApply]) &&
        !tree.tpe.isError && tree.tpe.isValueType && macros.isDefMacro(tree.symbol)

    def expanded: Tree = {
      // instantiate tvars as much as possible before macro expansion
      tree match {
        case tapply: tpd.TypeApply =>
          tapply.args.map(arg => Inferencing.isFullyDefined(arg.tpe, ForceDegree.noBottom))
        case _ =>
      }

      val res = forObject("scala.gestalt.dotty.Expander").apply("expandDefMacro", tree, ctx).asInstanceOf[Tree]
      debug.println(i"def macro expansion: $tree expands to $res")
      res
    }

    // trees with errors are possibly not well formed, which could result in macro expansion exception
    // e.g. macros with missing implicit arguments will take the expected value type instead of ImplicitMethod
    if (!ctx.reporter.hasErrors && isMacroApplyEnd)
      if (ctx.macrosEnabled) typer.typed(expanded, pt)
      else errorTree(tree, s"can't expand macro, make sure `scala.gestalt` is in -classpath")
    else tree
  }

  /** Transform macro definitions in class definition
   *
   *  @param tree  the tree that may contain macro definition, the tree may be a thicket
   *  @returns     the transformed tree
   *
   *  @note The returned tree NEEDs desugaring
   *
   */
  def transform(tree: Tree)(implicit ctx: Context): Tree = {
    tree match {
      case cdef: TypeDef if cdef.isClassDef =>
        Transform.transform(cdef)
      case mdef: ModuleDef =>
        Transform.transform(mdef)
      case thicket: Thicket =>
        Thicket(thicket.trees.map(transform))
      case _ =>
        tree
    }
  }
}
