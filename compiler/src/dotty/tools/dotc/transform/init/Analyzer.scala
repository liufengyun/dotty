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

object Analyzer {
  def isPartial(tp: Type)(implicit ctx: Context) = tp.dealiasKeepAnnots.hasAnnotation(defn.PartialAnnot)
  def isFilled(tp: Type)(implicit ctx: Context) = tp.dealiasKeepAnnots.hasAnnotation(defn.FilledAnnot)

  def isPartial(sym: Symbol)(implicit ctx: Context) = sym.hasAnnotation(defn.PartialAnnot)
  def isFilled(sym: Symbol)(implicit ctx: Context) = sym.hasAnnotation(defn.FilledAnnot)
  def isInit(sym: Symbol)(implicit ctx: Context) = sym.hasAnnotation(defn.InitAnnot)

  def isPrimaryConstructorFields(sym: Symbol)(implicit ctx: Context) = sym.is(ParamAccessor)

  def typeState(tp: Type)(implicit ctx: Context) =
    if (isPartial(tp)) State.Partial
    else if (isFilled(tp)) State.Filled
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

  def objectInfo(id: Int, static: Boolean = false) = ObjectInfo {
    (sym: Symbol, heap: Heap, pos: Position) =>
      if (static) Rules.selectStatic(heap(env.id), sym)
      else Rules.selectDynamic(heap(env.id), sym)
  }

  def setupConstructorEnv(outerEnv: Env, cls: ClassSymbol, tmpl: Template, analyzer: Analyzer, static: Boolean = false)(implicit ctx: Context) = {
    val env = outerEnv.newEnv
    val accessors = cls.paramAccessors.filterNot(x => x.isSetter)

    for (param <- accessors)
      env.add(param, SymInfo(assigned = true, state = typeState(sym.info)))

    // non-initialized fields of current class, state information on them
    // should be ignored for data-flow analysis.
    for (decl <- cls.info.decls.toList if isNonParamField(decl))
      env.add(param, SymInfo(assigned = false))

    analyzer.indexStats(tmpl.body, env)

    val thisInfo =  objectInfo(env.id, cls.isEffectivelyFinal || static)
    outerEnv.add(cls, SymInfo(state = State.Partial, latentInfo = thisInfo))

    env
  }

  /*
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
  } */

  // TODO: default methods are not necessarily safe, if they call other methods
  def isDefaultGetter(sym: Symbol)(implicit ctx: Context) = sym.name.is(NameKinds.DefaultGetterName)

  def hasPartialParam(cls: ClassSymbol)(implicit ctx: Context): Boolean =
    cls.paramAccessors.exists(_.hasAnnotation(defn.PartialAnnot))

  object NewEx {
    def extract(tp: Type)(implicit ctx: Context): TypeRef = tp.dealias match {
      case tref: TypeRef => tref
      case AppliedType(tref: TypeRef, targs) => tref
    }

    def unapply(tree: tpd.Tree)(implicit ctx: Context): Option[(TypeRef, TermRef, List[List[tpd.Tree]])] = {
      val (fn, targs, vargss) = tpd.decomposeCall(tree)
      if (!fn.symbol.isConstructor || !tree.isInstanceOf[tpd.Apply]) None
      else {
        val Select(New(tpt), _) = fn
        Some((extract(tpt.tpe),  fn.tpe.asInstanceOf[TermRef], vargss))
      }
    }
  }
}

object Rules {
  def selectDynamic(env: Env, sym: Symbol, pos: Position): Res =
    if (env.contains(sym)) {
      if (sym.is(Lazy)) selectLocalLazy(env, sym, pos)
      else if (sym.is(Method)) {
        var effs = Vector.empty[Effect]

        if (!sym.hasAnnotation(defn.PartialAnnot) && !sym.isEffectivelyFinal)
          effs = effs :+ OverrideRisk(sym, pos)

        val res = selectLocalMethod(env, sym, pos)
        res ++= effs
        res
      }
      else selectLocalField(env, sym, pos)
    }
    else // select on super
      if (sym.is(Lazy)) selectFilledLazy(env, sym, pos)
      else if (sym.is(Method)) selectFilledMethod(env, sym, pos)
      else selectFilledField(env, sym, pos)


  def selectStatic(env: Env, sym: Symbol, pos: Position): Res =
    if (env.contains(sym)) {
      if (sym.is(Lazy)) selectLocalLazy(env, sym, pos)
      else if (sym.is(Method)) selectLocalMethod(env, sym, pos)
      else selectLocalField(env, sym, pos)
    }
    else // select on super
      if (sym.is(Lazy)) selectFilledLazy(env, sym, pos)
      else if (sym.is(Method)) selectFilledMethod(env, sym, pos)
      else selectFilledField(env, sym, pos)


  def selectFilledField(sym: Symbol, pos: Position): Res =
    Res(state = typeState(sym.info))

  def selectFilledLazy(sym: Symbol, pos: Position): Res =
    if (isFilled(sym) || isPartial(sym))
      Res(state = typeState(sym.info))
    else
      Res(effects = Vector(Generic("The lazy field should be marked as `@partial` or `@filled` in order to be accessed", pos)))

  def selectFilledMethod(sym: Symbol, pos: Position): Res =
    if (!isFilled(sym) || !isPartial(sym))
      Res(effects = Vector(Generic("The method should be marked as `@partial` or `@filled` in order to be called", pos)))
    else if (sym.info.isInstanceOf[ExprType]) {   // parameter-less call
      Res(state = typeState(sym.info.widenExpr))
    }
    else Res()

  def selectLocalField(env: Env, sym: Symbol, pos: Position): Res = {
    val symInfo = env(sym)

    var effs = Vector.empty[Effect]
    if (!env.isAssigned(sym)) effs = effs :+ Uninit(sym, pos)

    if (sym.is(Deferred) && !sym.hasAnnotation(defn.InitAnnot))
      effs = effs :+ UseAbstractDef(sym, pos)

    Res(effects = effs, state = symInfo.state, latenInfo = symInfo.latentInfo)
  }

  def selectLocalMethod(env: Env, sym: Symbol, pos: Position): Res = {
    val symInfo = env(sym)
    if (sym.info.isInstanceOf[ExprType]) {       // parameter-less call
      val latentInfo = symInfo.latentInfo.asMethod
      val res2 = latentInfo(i => null, env.heap)

      if (res2.effects.nonEmpty)
        res2.effects = Vector(Call(sym, res2.effects, pos))

      res2
    }
    else Res(effects, latentInfo = symInfo.latentInfo)
  }

  def selectLocalLazy(env: Env, sym: Symbol, pos: Position): Res = {
    val symInfo = env(sym)
    if (!symInfo.isForced) {
      env.setForced(symInfo)
      indentedDebug(s">>> forcing $sym")
      val res = symInfo.latentInfo.asMethod.apply(i => null, env.heap)
      env(sym) = symInfo.copy(state = res.state, latenInfo = res.latenInfo)
    }
    else Res(state = symInfo.state, latentInfo = symInfo.latentInfo)
  }

  def call(valInfofn: Int => ValueInfo, heap: Heap)(implicit ctx: Context): Res = {
    latentInfo.asMethod.apply(valInfofn, heap)
  }

  def select(res: Res, sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    if (res.isLatent) {
      if (res.latentInfo.isObject) res.latentInfo.asObject.select(sym, heap, pos)
      else {
        assert(sym.name.toString == "apply")
        Res(latentInfo = res.latentInfo, effects = res.effects) // closures
      }
    }
    else {
      if (res.isPartial) {
        if (sym.is(Method)) {
          if (!Analyzer.isPartial(sym))
            res += Generic("The method should be marked as `@partial` in order to be called", pos)
        }
        else if (sym.is(Lazy)) {
          if (!Analyzer.isPartial(sym))
            res += Generic("The lazy field should be marked as `@partial` in order to be accessed", pos)
        }
        else {
          if (!Analyzer.isPrimaryConstructorFields(sym) && !sym.owner.is(Trait))
            res += Generic("Cannot access fields on a partial object", pos)
        }
      }
      else if (res.isFilled) {
        if (sym.is(Method)) {
          if (!Analyzer.isPartial(sym) || !Analyzer.isFilled(sym))
            res += Generic("The method should be marked as `@partial` or `@filled` in order to be called", pos)
          res
        }
        else if (sym.is(Lazy)) {
          if (!Analyzer.isPartial(sym) || !Analyzer.isFilled(sym))
            res += Generic("The lazy field should be marked as `@partial` or `@filled` in order to be accessed", pos)

          Res(state = Analyzer.typeState(sym.info), effects = res.effects)
        }
        else {
          if (!Analyzer.isPrimaryConstructorFields(sym) && !sym.owner.is(Trait))
            res += Generic("Cannot access fields on a partial object", pos)

          Res(state = Analyzer.typeState(sym.info), effects = res.effects)
        }
    }
    else Res()
  }
}

class Analyzer {
  import tpd._

  var depth: Int = 0
  val indentTab = " "

  def trace[T](msg: String, env: Env)(body: => T) = {
    indentedDebug(s"==> ${pad(msg)}?")
    indentedDebug(env.toString)
    depth += 1
    val res = body
    depth -= 1
    indentedDebug(s"<== ${pad(msg)} = ${pad(res.toString)}")
    res
  }

  def padding = indentTab * depth

  def pad(s: String, padFirst: Boolean = false) =
    s.split("\n").mkString(if (padFirst) padding else "", "\n" + padding, "")

  def indentedDebug(msg: String) = debug(pad(msg, padFirst = true))

  def checkParams(sym: Symbol, paramInfos: List[Type], args: List[Tree], env: Env, force: Boolean)(implicit ctx: Context): (Res, Vector[ValueInfo]) = {
    def isParamPartial(index: Int) = paramInfos(index).dealiasKeepAnnots.hasAnnotation(defn.PartialAnnot)

    var effs = Vector.empty[Effect]
    var infos = Vector.empty[ValueInfo]
    var partial = false

    args.zipWithIndex.foreach { case (arg, index) =>
      val res = apply(arg, env)
      effs ++= res.effects
      partial = partial || res.isPartial
      infos = infos :+ ValueInfo(res.isPartial, res.latentInfo)

      if (res.isLatent && force) {
        val effs2 = res.force(i => ValueInfo(), env.heap)            // latent values are not partial
        if (effs2.effects.nonEmpty) {
          partial = true
          if (!isParamPartial(index)) effs = effs :+ Latent(arg, effs2.effects)
        }
      }
      if (res.isPartial && !isParamPartial(index) && force) effs = effs :+ Argument(sym, arg)
    }

    (Res(effects = effs, partial = partial), infos)
  }

  def checkNew(tree: Tree, tref: TypeRef, init: TermRef, argss: List[List[tpd.Tree]], env: Env)(implicit ctx: Context): Res = {
    val paramInfos = init.widen.paramInfoss.flatten
    val args = argss.flatten

    val (res1, _) = checkParams(tref.symbol, paramInfos, args, env, force = true)

    if (tref.symbol == env.currentClass) {
      res1 += RecCreate(tref.symbol, tree)
      return res1
    }

    if (!(localRef(tref, env).exists)) return res1

    if (!isLexicalRef(tref, env)) {
      if (isPartial(tref.prefix, env) && !isSafeVirtualAccess(tref, env))
        res1 += PartialNew(tref.prefix, tref.symbol, tree.pos)
      res1
    }
    else {
      indentedDebug(s">>> create new instance ${tref.symbol}")
      val latentInfo = env.latentInfo(tref.symbol).asMethod
      val res2 = latentInfo(i => null, env.heap)               // TODO: propagate params to init
      if (res2.effects.nonEmpty && !ctx.owner.is(Synthetic)) res2 += Instantiate(tref.symbol, res2.effects, tree.pos)
      res2
    }
  }

  def checkApply(tree: tpd.Tree, fun: Tree, argss: List[List[Tree]], env: Env)(implicit ctx: Context): Res = {
    val res1 = apply(fun, env)

    val args = argss.flatten
    val paramInfos = fun.tpe.widen.paramInfoss.flatten
    val (res2, valueInfos) = checkParams(fun.symbol, paramInfos, args, env, force = !res1.isLatent)

    var effs = res1.effects ++ res2.effects

    if (res1.isLatent) {
      indentedDebug(s">>> calling ${fun.symbol}")
      val res3 = res1.force(i => valueInfos(i), env.heap)
      if (res3.effects.nonEmpty) effs = effs :+ Latent(tree, res3.effects)

      res3.copy(effects = effs)
    }
    else Res(effects = effs)
  }

  def checkSelect(tree: Select, env: Env)(implicit ctx: Context): Res = {
    val prefixRes = apply(tree.qualifier, env)

    val res = Rules.select(prefixRes, tree.symbol, env.heap, tree.pos)
    res ++= prefixRes.effects

    res
  }

  /** return the top-level local term within `cls` refered by `tp`, NoType otherwise.
   *
   *  There are following cases:
   *   - select on this: `C.this.x`
   *   - select on super: `C.super[Q].x`
   *   - local ident: `x`
   *   - select on self: `self.x` (TODO)
   */
  def localRef(tp: Type, env: Env)(implicit ctx: Context): Type = tp match {
    case NamedTypeEx(ThisType(tref), _) if tref.symbol.isContainedIn(env.currentClass) => tp
    case NamedTypeEx(SuperType(ThisType(tref), _), _) if tref.symbol.isContainedIn(env.currentClass) => tp
    case ref @ NamedTypeEx(NoPrefix, _) if ref.symbol.isContainedIn(env.currentClass) => ref
    case ref @ NamedTypeEx(tp: TermRef, _) =>
      if (tp <:< env.currentClass.thisType) ref    // tp is alias of `this`
      else localRef(tp, env)
    case _ => NoType
  }

  object NamedTypeEx {
    def unapply(tp: NamedType)(implicit ctx: Context): Option[(Type, Symbol)] = tp match {
      case ref: TermRef => Some(ref.prefix -> ref.symbol)
      case ref: TypeRef => Some(ref.prefix -> ref.symbol)
      case _ => None
    }
  }

  def checkRef(tp: Type, env: Env, pos: Position)(implicit ctx: Context): Res = tp match {
    case tp @ TermRef(NoPrefix, _) =>
      val sym = tp.symbol
      if (env.contains(sym)) {
        if (sym.is(Lazy)) selectLocalLazy(env, sym, pos)
        else if (sym.is(Method)) selectLocalMethod(env, sym, pos)
        else selectLocalField(env, sym, pos)
      }
      else Res()
    case tp @ TermRef(prefix, _) =>
      val res = checkRef(prefix, env, pos)
      res.select(tp.symbol, env.heap, pos)
    case tp @ ThisType(tref) =>
      val cls = tref.symbol
      if (env.contains(sym)) Res(latenInfo = env(cls).latenInfo)
      else Res() // TODO: all outer `this` should be in environment
    case tp @ SuperType(thistpe, supertpe) =>
      // TODO : handle `supertpe`
      checkRef(ThisType(thistpe), env, pos)
  }

  def checkClosure(sym: Symbol, tree: Tree, env: Env)(implicit ctx: Context): Res =
    Res(latentInfo = env(sym).latenInfo)

  def checkIf(tree: If, env: Env)(implicit ctx: Context): Res = {
    val If(cond, thenp, elsep) = tree

    val res1: Res = apply(cond, env)

    val envClone = env.deepClone
    val res2: Res = apply(thenp, env)
    val res3: Res = apply(elsep, envClone)

    env.heap.join(envClone.heap)

    res2.copy(effects = res1.effects ++ res2.effects).join(res3)
  }

  def checkValDef(vdef: ValDef, env: Env)(implicit ctx: Context): Res = {
    val rhsRes = apply(vdef.rhs, env)

    if (!tpd.isWildcardArg(vdef.rhs) && !vdef.rhs.isEmpty)
      env.setAssigned(vdef.symbol)     // take `_` as uninitialized, otherwise it's initialized

    val symInfo = env(vdef.symbol)
    env(vdef.symbol) = symInfo.copy(latenInfo = rhsRes.latentInfo, state = rhsRes.state)

    Res(effects = rhsRes.effects)
  }

  def checkStats(stats: List[Tree], env: Env)(implicit ctx: Context): Res =
    stats.foldLeft(Res()) { (acc, stat) =>
      indentedDebug(s"acc = ${pad(acc.toString)}")
      val res1 = apply(stat, env)
      acc.copy(effects = acc.effects ++ res1.effects)
    }

  def checkBlock(tree: Block, env: Env)(implicit ctx: Context): Res = {
    val env2 = env.heap.newEnv(env.id)
    indexStats(tree.stats, env2)

    val res1 = checkStats(tree.stats, env2)
    val res2 = apply(tree.expr, env2)

    res2.copy(effects = res1.effects ++ res2.effects)
  }

  // TODO: method call should compute fix point
  protected var _methChecking: Set[Symbol] = Set()
  def isChecking(sym: Symbol)   = _methChecking.contains(sym)
  def checking[T](sym: Symbol)(fn: => T) = {
    _methChecking += sym
    val res = fn
    _methChecking -= sym
    res
  }

  def indexClassDef(tdef: TypeDef, env: Env)(implicit ctx: Context): Unit = {
    val tmpl = tdef.rhs.asInstanceOf[Template]

    def nonStaticStats = tmpl.body.filter {
      case vdef : ValDef  =>
        !vdef.symbol.hasAnnotation(defn.ScalaStaticAnnot)
      case stat =>
        true
    }

    // TODO
    //   - handle params to init
    //   - handle parent calls
    //   - handle 2nd constructor
    val latent = MethodInfo { (valInfoFn, heap) =>
      if (isChecking(tdef.symbol)) {
        debug(s"recursive creation of ${tdef.symbol} found during initialization of ${env.currentClass}")
        Res()
      }
      else checking(tdef.symbol) {
        val outerEnv = heap(env.id)
        val env = Analyzer.setupConstructorEnv(outerEnv, tdef.symbol, tmpl, this, static = true)

        val res = apply(tmpl, outerEnv)(ctx.withOwner(tdef.symbol))
        Res(latenInfo = Analyzer.objectInfo(env.id, static = true), effects = res.effects)
      }
    }
    env.add(tdef.symbol.primaryConstructor, SymInfo(latentInfo = latent))
  }

  def indexStats(stats: List[Tree], env: Env)(implicit ctx: Context): Unit = stats.foreach {
    case ddef: DefDef if ddef.symbol.is(AnyFlags, butNot = Accessor) =>
      val latenInfo = MethodInfo { (valInfoFn, heap) =>
        if (isChecking(ddef.symbol)) {
          // TODO: force latent effects on arguments
          debug(s"recursive call of ${ddef.symbol} found during initialization of ${env.currentClass}")
          Res()
        }
        else {
          val env2 = env.newEnv(heap)
          ddef.vparamss.flatten.zipWithIndex.foreach { case (param: ValDef, index: Int) =>
            val ValueInfo(state, latentInfo) = valInfoFn(index)
            env2.add(param.symbol, SymInfo(assigned = true, state = state, latentInfo = latentInfo))
          }

          checking(ddef.symbol) { apply(ddef.rhs, env2)(ctx.withOwner(ddef.symbol)) }
        }
      }

      env.add(ddef.symbol, SymInfo(latenInfo = latenInfo))
    case vdef: ValDef if vdef.symbol.is(Lazy)  =>
      val latent = MethodInfo { (valInfoFn, heap) =>
        val env2 = heap(env.id)
        if (isChecking(vdef.symbol)) {
          debug(s"recursive forcing of lazy ${vdef.symbol} found during initialization of ${env.currentClass}")
          Res()
        }
        else checking(vdef.symbol) {
          apply(vdef.rhs, env2)
        }
      }
      env.add(vdef.symbol,  SymInfo(latenInfo = latenInfo))
    case tdef: TypeDef if tdef.isClassDef  =>
      indexClassDef(tdef, env)
    case _ =>
  }

  def apply(tree: Tree, env: Env)(implicit ctx: Context): Res = trace("checking " + tree.show, env)(tree match {
    case tmpl: Template =>
      // TODO: check parents
      checkStats(tmpl.body, env)
    case vdef : ValDef if !vdef.symbol.is(Lazy) =>
      checkValDef(vdef, env)
    case _: DefTree =>  // ignore other definitions
      Res()
    case Closure(_, meth, _) =>
      checkClosure(meth.symbol, tree, env)
    case tree: Ident if tree.symbol.isTerm =>
      checkRef(tree.tpe, env, tree.pos)
    case tree @ This(tref) =>
      checkRef(tree.tpe, env, tree.pos)
    case tree @ Super(qual, mix) =>
      checkRef(tree.tpe, env, tree.pos)
    case tree @ Select(prefix, _) if tree.symbol.isTerm =>
      checkSelect(tree, env)
    case tree @ If(cond, thenp, elsep) =>
      checkIf(tree, env)
    case tree @ Apply(_, _) =>
      val (fn, targs, vargss) = decomposeCall(tree)
      checkApply(tree, fn, vargss, env)
    case tree @ NewEx(tref, init, argss) =>
      checkNew(tree, tref, init, argss, env)
    case tree @ Assign(lhs @ (Ident(_) | Select(This(_), _)), rhs) =>
      val resRhs = apply(rhs, env)

      if (!resRhs.isPartial || env.isPartial(lhs.symbol) || env.isNotInit(lhs.symbol)) {
        if (env.isNotInit(lhs.symbol)) env.addInit(lhs.symbol)
        if (!resRhs.isPartial) env.removePartial(lhs.symbol)
        else env.addPartial(lhs.symbol)
      }
      else resRhs += CrossAssign(lhs, rhs)

      resRhs.copy(partial = false, latentInfo = null)
    case tree @ Assign(lhs @ Select(prefix, _), rhs) =>
      val resLhs = apply(prefix, env)
      val resRhs = apply(rhs, env)

      val res = Res(effects = resLhs.effects ++ resRhs.effects)

      if (resRhs.isPartial && !resLhs.isPartial)
        res += CrossAssign(lhs, rhs)

      res
    case tree @ Block(stats, expr) =>
      checkBlock(tree, env)
    case Typed(expr, tpd) =>
      apply(expr, env)
    case _ =>
      Res()
  })
}