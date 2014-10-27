package dotty.tools.dotc
package transform

import TreeTransforms._
import core._
import DenotTransformers._
import Symbols._
import SymDenotations._
import Contexts._
import Types._
import Flags._
import Decorators._
import SymUtils._
import util.Attachment
import core.StdNames.nme
import ast.Trees._

object ElimByName {
  val ByNameArg = new Attachment.Key[Unit]
}

/** This phase eliminates ExprTypes `=> T` as types of function parameters, and replaces them by
 *  nullary function types.  More precisely:
 *
 *  For the types of parameter symbols:
 *
 *      => T        ==>    () => T
 *
 *  Note that `=> T` types are not eliminated in MnethodTypes. This is done later at erasure.
 *  Terms are rewritten as follows:
 *
 *      x           ==>    x.apply()   if x is a parameter that had type => T
 *
 *  Arguments to call-by-name parameters are translated as follows. First, the argument is
 *  rewritten by the rules
 *
 *      e.apply()   ==>    e           if e.apply() is an argument to a call-by-name parameter
 *      expr        ==>    () => expr  if other expr is an argument to a call-by-name parameter
 *
 *  This makes the argument compatible with a parameter type of () => T, which will be the
 *  formal parameter type at erasure. But to be -Ycheckable until then, any argument
 *  ARG rewritten by the rules above is again wrapped in an application ARG.apply(),
 *  labelled with an `ByNameParam` attachment.
 *
 *  Erasure will later strip wrapped `.apply()` calls with ByNameParam attachments.
 *
 */
class ElimByName extends MiniPhaseTransform with InfoTransformer { thisTransformer =>
  import ast.tpd._
  import ElimByName._

  override def phaseName: String = "elimByName"

  override def runsAfterGroupsOf = Set(classOf[Splitter])
    // assumes idents and selects have symbols; interferes with splitter distribution
    // that's why it's "after group".

  override def treeTransformPhase = thisTransformer.next

  /** The info of the tree's symbol at phase Nullarify (i.e. before transformation) */
  private def originalDenotation(tree: Tree)(implicit ctx: Context) =
    tree.symbol.denot(ctx.withPhase(thisTransformer))

  override def transformApply(tree: Apply)(implicit ctx: Context, info: TransformerInfo): Tree =
    ctx.traceIndented(s"transforming ${tree.show} at phase ${ctx.phase}", show = true) {

    def transformArg(arg: Tree, formal: Type): Tree = formal.dealias match {
      case formalExpr: ExprType =>
        val argFun = arg match {
          case Apply(Select(qual, nme.apply), Nil) if qual.tpe derivesFrom defn.FunctionClass(0) =>
            qual
          case _ =>
            val meth = ctx.newSymbol(
                ctx.owner, nme.ANON_FUN, Synthetic | Method, MethodType(Nil, Nil, arg.tpe.widen))
            Closure(meth, _ => arg.changeOwner(ctx.owner, meth))
        }
        val argApplied = argFun.select(defn.Function0_apply).appliedToNone
        argApplied.putAttachment(ByNameArg, ())
        argApplied
      case _ =>
        arg
    }

    val MethodType(_, formals) = tree.fun.tpe.widen
    val args1 = tree.args.zipWithConserve(formals)(transformArg)
    cpy.Apply(tree)(tree.fun, args1)
  }

  /** If denotation had an ExprType before, it now gets a function type */
  private def exprBecomesFunction(symd: SymDenotation)(implicit ctx: Context) =
    (symd is Param) || (symd is (ParamAccessor, butNot = Method))

  /** Map `tree` to `tree.apply()` is `ftree` was of ExprType and becomes now a function */
  private def applyIfFunction(tree: Tree, ftree: Tree)(implicit ctx: Context) = {
    val origDenot = originalDenotation(ftree)
    if (exprBecomesFunction(origDenot) && (origDenot.info.isInstanceOf[ExprType]))
      tree.select(defn.Function0_apply).appliedToNone
    else tree
  }

  override def transformIdent(tree: Ident)(implicit ctx: Context, info: TransformerInfo): Tree =
    applyIfFunction(tree, tree)

  override def transformTypeApply(tree: TypeApply)(implicit ctx: Context, info: TransformerInfo): Tree = tree match {
    case TypeApply(Select(_, nme.asInstanceOf_), arg :: Nil) =>
      // tree might be of form e.asInstanceOf[x.type] where x becomes a function.
      // See pos/t296.scala
      applyIfFunction(tree, arg)
    case _ => tree
  }

  override def transformValDef(tree: ValDef)(implicit ctx: Context, info: TransformerInfo): Tree =
    if (exprBecomesFunction(tree.symbol))
      cpy.ValDef(tree)(tpt = tree.tpt.withType(tree.symbol.info))
    else tree

  def transformInfo(tp: Type, sym: Symbol)(implicit ctx: Context): Type = tp match {
    case ExprType(rt) if exprBecomesFunction(sym) => defn.FunctionType(Nil, rt)
    case _ => tp
  }
}
