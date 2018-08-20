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

  def symbolState(sym: Symbol)(implicit ctx: Context) =
    if (isPartial(sym)) State.Partial
    else if (isFilled(sym)) State.Filled
    else State.Full

  def isConcreteField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Deferred | Method | Local | Private)

  def isNonParamField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Method | ParamAccessor | Lazy | Deferred)

  def isField(sym: Symbol)(implicit ctx: Context) =
    sym.isTerm && sym.is(AnyFlags, butNot = Method | Lazy | Deferred)

  def addOuterThis(cls: ClassSymbol, env: Env)(implicit ctx: Context) = {
    def recur(cls: Symbol, maxState: State): Unit = if (cls.owner.exists) {
      val outerState = symbolState(cls)
      val enclosingCls = cls.owner.enclosingClass

      if (!cls.owner.isClass || maxState.isFull) {
        env.add(enclosingCls, SymInfo(state = State.Full))
        recur(enclosingCls, State.Full)
      }
      else {
        env.add(enclosingCls, SymInfo(state = State.max(outerState, maxState)))
        recur(enclosingCls, State.max(outerState, maxState))
      }
    }
    recur(cls, State.Partial)
  }

  // TODO: should we pass context as function arguments?
  def objectInfo(id: Int, static: Boolean = false)(implicit ctx: Context) =
    ObjectInfo(
      (sym: Symbol, heap: Heap, pos: Position) => {
        // println(s"select $sym from:\n" + heap(id).toString)
        if (static) Rules.selectStatic(heap(id), sym, pos)
        else Rules.selectDynamic(heap(id), sym, pos)
      },
      (sym: Symbol, valInfo: ValueInfo, heap: Heap) => {
        heap(id)(sym) = SymInfo(
          assigned = true,
          state = valInfo.state,
          latentInfo = valInfo.latentInfo
        )
      }
    )
}

object Rules {
  def selectDynamic(env: Env, sym: Symbol, pos: Position)(implicit ctx: Context): Res =
    if (env.contains(sym)) { // TODO: selection on self annotation
      debug("select dynamic-dispatch symbol " + sym)
      if (sym.is(Lazy)) selectLocalLazy(env, sym, pos)
      else if (sym.is(Method)) {
        val res = selectLocalMethod(env, sym, pos)

        if (!sym.hasAnnotation(defn.PartialAnnot) && !sym.isEffectivelyFinal)
          res += OverrideRisk(sym, pos)

        res
      }
      else if (sym.isClass) selectLocalClass(env, sym, pos)
      else {
        val res = selectLocalField(env, sym, pos)

        if (sym.is(Deferred) && !sym.hasAnnotation(defn.InitAnnot))
          res += UseAbstractDef(sym, pos)

        res
      }
    }
    else { // select on super
      if (sym.is(Lazy)) selectFilledLazy(sym, pos)
      else if (sym.is(Method)) selectFilledMethod(sym, pos)
      else if (sym.isClass) selectFilledClass(sym, pos)
      else selectFilledField(sym, pos)
    }

  def selectStatic(env: Env, sym: Symbol, pos: Position)(implicit ctx: Context): Res =
    if (env.contains(sym)) { // TODO: selection on self annotation
      debug("select static-dispatch symbol " + sym)
      if (sym.is(Lazy)) selectLocalLazy(env, sym, pos)
      else if (sym.is(Method)) selectLocalMethod(env, sym, pos)
      else if (sym.isClass) selectLocalClass(env, sym, pos)
      else selectLocalField(env, sym, pos)
    }
    else { // select on super
      if (sym.is(Lazy)) selectFilledLazy(sym, pos)
      else if (sym.is(Method)) selectFilledMethod(sym, pos)
      else if (sym.isClass) selectFilledClass(sym, pos)
      else selectFilledField(sym, pos)
    }

  def selectFilledClass(sym: Symbol, pos: Position)(implicit ctx: Context): Res =
    if (Analyzer.isFilled(sym) || Analyzer.isPartial(sym))
      Res()
    else
      Res(effects = Vector(Generic(s"Annotate the nested $sym with `@partial` or `@filled`", pos)))

  def selectFilledField(sym: Symbol, pos: Position)(implicit ctx: Context): Res =
    Res(state = Analyzer.typeState(sym.info))

  def selectFilledLazy(sym: Symbol, pos: Position)(implicit ctx: Context): Res =
    if (Analyzer.isFilled(sym) || Analyzer.isPartial(sym))
      Res(state = Analyzer.typeState(sym.info))
    else
      Res(effects = Vector(Generic("The lazy field should be marked as `@partial` or `@filled` in order to be accessed", pos)))

  def selectFilledMethod(sym: Symbol, pos: Position)(implicit ctx: Context): Res =
    if (!Analyzer.isFilled(sym) || !Analyzer.isPartial(sym))
      Res(effects = Vector(Generic("The method should be marked as `@partial` or `@filled` in order to be called", pos)))
    else if (sym.info.isInstanceOf[ExprType]) {   // parameter-less call
      Res(state = Analyzer.typeState(sym.info.widenExpr))
    }
    else Res()

  def selectLocalClass(env: Env, sym: Symbol, pos: Position): Res =
    Res(latentInfo = env(sym).latentInfo)

  def selectLocalField(env: Env, sym: Symbol, pos: Position): Res = {
    val symInfo = env(sym)

    var effs = Vector.empty[Effect]
    if (!env.isAssigned(sym)) effs = effs :+ Uninit(sym, pos)

    Res(effects = effs, state = symInfo.state, latentInfo = symInfo.latentInfo)
  }

  def selectLocalMethod(env: Env, sym: Symbol, pos: Position)(implicit ctx: Context): Res = {
    val symInfo = env(sym)
    if (sym.info.isInstanceOf[ExprType]) {       // parameter-less call
      val latentInfo = symInfo.latentInfo.asMethod
      val res2 = latentInfo(i => null, env.heap)

      if (res2.effects.nonEmpty)
        res2.effects = Vector(Call(sym, res2.effects, pos))

      res2
    }
    else Res(latentInfo = symInfo.latentInfo)
  }

  def selectLocalLazy(env: Env, sym: Symbol, pos: Position): Res = {
    val symInfo = env(sym)
    if (!symInfo.forced) {
      val res = symInfo.latentInfo.asMethod.apply(i => null, env.heap)
      env(sym) = symInfo.copy(forced = true, state = res.state, latentInfo = res.latentInfo)

      if (res.hasErrors) Res(effects = Vector(Force(sym, res.effects, pos)))
      else Res(state = res.state, latentInfo = res.latentInfo)
    }
    else Res(state = symInfo.state, latentInfo = symInfo.latentInfo)
  }

  def select(res: Res, sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    if (res.hasErrors) res
    else if (res.isLatent) {
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
            res += Generic(s"The $sym should be marked as `@partial` in order to be called", pos)
        }
        else if (sym.is(Lazy)) {
          if (!Analyzer.isPartial(sym))
            res += Generic(s"The lazy field $sym should be marked as `@partial` in order to be accessed", pos)
        }
        else if (sym.isClass) {
          if (!Analyzer.isPartial(sym))
            res += Generic(s"The nested $sym should be marked as `@partial` in order to be instantiated", pos)
        }
        else {
          if (!Analyzer.isPrimaryConstructorFields(sym) && !sym.owner.is(Trait))
            res += Generic(s"Cannot access field $sym on a partial object", pos)
        }

        // set state to Full, don't report same error message again
        Res(state = State.Full, effects = res.effects)
      }
      else if (res.isFilled) {
        if (sym.is(Method)) {
          if (!Analyzer.isPartial(sym) || !Analyzer.isFilled(sym))
            res += Generic(s"The method $sym should be marked as `@partial` or `@filled` in order to be called", pos)

          Res(state = State.Full, effects = res.effects)
        }
        else if (sym.is(Lazy)) {
          if (!Analyzer.isPartial(sym) || !Analyzer.isFilled(sym))
            res += Generic(s"The lazy field $sym should be marked as `@partial` or `@filled` in order to be accessed", pos)

          Res(state = Analyzer.typeState(sym.info), effects = res.effects)
        }
        else if (sym.isClass) {
          if (!Analyzer.isPartial(sym) || !Analyzer.isFilled(sym))
            res += Generic(s"The nested $sym should be marked as `@partial` or `@filled` in order to be instantiated", pos)

          Res(effects = res.effects)
        }
        else {
          if (!Analyzer.isPrimaryConstructorFields(sym) && !sym.owner.is(Trait))
            res += Generic(s"Cannot access field $sym on a partial object", pos)

          Res(state = Analyzer.typeState(sym.info), effects = res.effects)
        }
      }
      else Res()
    }
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

  def checkNew(tree: Tree, tref: TypeRef, init: TermRef, argss: List[List[Tree]], env: Env)(implicit ctx: Context): Res = {
    val cls = tref.classSymbol
    val prefixRes = checkRef(tref.prefix, env, tree.pos)
    val clsRes = Rules.select(prefixRes, cls, env.heap, tree.pos)

    if (clsRes.hasErrors) return clsRes

    val paramInfos = init.widen.paramInfoss.flatten
    val args = argss.flatten

    // check params
    var effs = Vector.empty[Effect]
    val valInfos = args.map { arg =>
      val res = apply(arg, env)
      effs = effs ++ res.effects
      ValueInfo(res.state, res.latentInfo)
    }

    if (effs.size > 0) return Res(effects = effs)

    val initRes = Rules.select(prefixRes, init.symbol, env.heap, tree.pos)
    if (initRes.isLatent) {
      indentedDebug(s">>> create new instance $cls")
      val res = initRes.latentInfo.asMethod(valInfos, env.heap)
      if (res.hasErrors) res.effects = Vector(Instantiate(cls, res.effects, tree.pos))
      res
    }
    else {
      val paramRes = checkParams(cls, valInfos, paramInfos, env, args.map(_.pos))
      if (paramRes.hasErrors) return paramRes

      if (!prefixRes.isFull || valInfos.exists(v => !v.isFull)) Res(state = State.Filled)
      else Res(state = State.Full)
    }
  }

  def force(latentInfo: LatentInfo, heap: Heap, pos: Position): Res = {
    // TODO: better handle latent objects
    if (latentInfo.isObject)
      return Res(effects = Vector(Generic("Leak of object under initialization", pos)))

    val res = latentInfo.asMethod(i => ValueInfo(), heap)
    if (res.hasErrors) res  // fewer errors at one place
    else if (res.isLatent) force(res.latentInfo, heap, pos)
    else Res()
  }

  def checkParams(sym: Symbol, valInfos: List[ValueInfo], paramInfos: List[Type], env: Env, positions: List[Position])(implicit ctx: Context): Res = {
    def paramState(index: Int) = Analyzer.typeState(paramInfos(index))

    valInfos.zipWithIndex.foreach { case (valInfo, index) =>
      if (valInfo.isLatent && valInfo.latentInfo.isMethod) {
        val res = force(valInfo.latentInfo, env.heap, positions(index))
        if (res.hasErrors && !paramState(index).isPartial) return res   // report fewer error at one place
      }
      else if (valInfo.state < paramState(index))
        return Res(effects = Vector(Generic("Leak of object under initialization to " + sym, positions(index))))
    }

    Res()
  }

  def checkApply(tree: tpd.Tree, fun: Tree, argss: List[List[Tree]], env: Env)(implicit ctx: Context): Res = {
    val funSym = fun.symbol
    val funRes = apply(fun, env)

    // reduce reported errors
    if (funRes.hasErrors) return Res(effects = funRes.effects)

    val args = argss.flatten
    val paramInfos = fun.tpe.widen.paramInfoss.flatten

    // check params
    var effs = Vector.empty[Effect]
    val valInfos = args.map { arg =>
      val res = apply(arg, env)
      effs = effs ++ res.effects
      ValueInfo(res.state, res.latentInfo)
    }

    if (effs.size > 0) return Res(effects = effs)

    if (funRes.isLatent) {
      indentedDebug(s">>> calling $funSym")
      val res = funRes.latentInfo.asMethod(valInfos, env.heap)
      if (res.hasErrors) res.effects = Vector(Latent(tree, res.effects))
      res
    }
    else checkParams(funSym, valInfos, paramInfos, env, args.map(_.pos))
  }

  def checkSelect(tree: Select, env: Env)(implicit ctx: Context): Res = {
    val prefixRes = apply(tree.qualifier, env)

    // reduce reported errors
    if (prefixRes.hasErrors) return Res(effects = prefixRes.effects)

    Rules.select(prefixRes, tree.symbol, env.heap, tree.pos)
  }

  private def enclosedIn(curSym: Symbol, inSym: Symbol)(implicit ctx: Context): Boolean =
    curSym.exists && ((curSym `eq` inSym) || (enclosedIn(curSym.owner, inSym)))

  def checkRef(tp: Type, env: Env, pos: Position)(implicit ctx: Context): Res = tp match {
    case tp : TermRef if tp.symbol.is(Module) && enclosedIn(ctx.owner, tp.symbol.moduleClass) =>
      // self reference by name: object O { ... O.xxx }
      checkRef(ThisType.raw(ctx.owner.typeRef), env, pos)
    case tp @ TermRef(NoPrefix, _) =>
      val sym = tp.symbol
      if (env.contains(sym)) {
        if (sym.is(Lazy)) Rules.selectLocalLazy(env, sym, pos)
        else if (sym.is(Method)) Rules.selectLocalMethod(env, sym, pos)
        else Rules.selectLocalField(env, sym, pos)
      }
      else Res()
    case tp @ TermRef(prefix, _) =>
      val res = checkRef(prefix, env, pos)
      Rules.select(res, tp.symbol, env.heap, pos)
    case tp @ ThisType(tref) =>
      val cls = tref.symbol
      if (cls.is(Package)) Res() // Dotty represents package path by ThisType
      else {
        val symInfo = env(cls)
        Res(latentInfo = symInfo.latentInfo, state = symInfo.state)
      }
    case tp @ SuperType(thistpe, supertpe) =>
      // TODO : handle `supertpe`
      checkRef(thistpe, env, pos)
  }

  def checkClosure(sym: Symbol, tree: Tree, env: Env)(implicit ctx: Context): Res =
    Res(latentInfo = env(sym).latentInfo)

  def checkIf(tree: If, env: Env)(implicit ctx: Context): Res = {
    val If(cond, thenp, elsep) = tree

    val condRes: Res = apply(cond, env)

    val envClone = env.deepClone
    val thenRes: Res = apply(thenp, env)
    val elseRes: Res = apply(elsep, envClone)

    env.heap.join(envClone.heap)

    thenRes ++= condRes.effects
    thenRes.join(elseRes)
  }

  def checkValDef(vdef: ValDef, env: Env)(implicit ctx: Context): Res = {
    val rhsRes = apply(vdef.rhs, env)

    if (!tpd.isWildcardArg(vdef.rhs))
      env.setAssigned(vdef.symbol)     // take `_` as uninitialized, otherwise it's initialized

    val symInfo = env(vdef.symbol)
    env(vdef.symbol) = symInfo.copy(latentInfo = rhsRes.latentInfo, state = rhsRes.state)

    Res(effects = rhsRes.effects)
  }

  def checkStats(stats: List[Tree], env: Env)(implicit ctx: Context): Res =
    stats.foldLeft(Res()) { (acc, stat) =>
      indentedDebug(s"acc = ${pad(acc.toString)}")
      val res1 = apply(stat, env)
      acc.copy(effects = acc.effects ++ res1.effects)
    }

  def checkBlock(tree: Block, env: Env)(implicit ctx: Context): Res = {
    val newEnv = env.newEnv()
    indexStats(tree.stats, newEnv)

    val res1 = checkStats(tree.stats, newEnv)
    val res2 = apply(tree.expr, newEnv)

    res2.copy(effects = res1.effects ++ res2.effects)
  }

  protected var _methChecking: Set[Symbol] = Set()
  def isChecking(sym: Symbol)   = _methChecking.contains(sym)
  def checking[T](sym: Symbol)(fn: => T) = {
    _methChecking += sym
    val res = fn
    _methChecking -= sym
    res
  }

  def indexConstructors(cls: Symbol, tmpl: Template, env: Env)(implicit ctx: Context): Unit = {
    def nonStaticStats = tmpl.body.filter {
      case vdef : ValDef  =>
        !vdef.symbol.hasAnnotation(defn.ScalaStaticAnnot)
      case stat =>
        true
    }

    // primary constructor
    val latent = MethodInfo { (valInfoFn, heap) =>
      if (isChecking(cls)) {
        debug(s"recursive creation of $cls found")
        Res()
      }
      else checking(cls) {
        val outerEnv = heap(env.id)
        val newEnv = outerEnv.newEnv()

        tmpl.constr.vparamss.flatten.zipWithIndex.foreach { case (param: ValDef, index: Int) =>
          val ValueInfo(state, latentInfo) = valInfoFn(index)
          newEnv.add(param.symbol, SymInfo(assigned = true, state = state, latentInfo = latentInfo))
        }

        indexStats(nonStaticStats, newEnv)

        val thisInfo =  Analyzer.objectInfo(newEnv.id, static = true)
        outerEnv.add(cls, SymInfo(state = State.Partial, latentInfo = thisInfo))

        val res = apply(tmpl, newEnv)(ctx.withOwner(cls))
        Res(latentInfo = thisInfo, effects = res.effects, state = State.Filled)
      }
    }
    env.add(cls.primaryConstructor, SymInfo(latentInfo = latent))
    env.add(cls, SymInfo())

    // TODO: secondary constructor
    tmpl.body.foreach {
      case ddef: DefDef if ddef.symbol.isConstructor =>
      case _ =>
    }
  }

  def indexStats(stats: List[Tree], env: Env)(implicit ctx: Context): Unit = stats.foreach {
    case ddef: DefDef if ddef.symbol.is(AnyFlags, butNot = Accessor) && !ddef.symbol.isConstructor =>
      val latentInfo = MethodInfo { (valInfoFn, heap) =>
        if (isChecking(ddef.symbol)) {
          // TODO: force latent effects on arguments
          debug(s"recursive call of ${ddef.symbol} found")
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

      env.add(ddef.symbol, SymInfo(latentInfo = latentInfo))
    case vdef: ValDef if vdef.symbol.is(Lazy)  =>
      val latentInfo = MethodInfo { (valInfoFn, heap) =>
        val env2 = heap(env.id)
        if (isChecking(vdef.symbol)) {
          debug(s"recursive forcing of lazy ${vdef.symbol} found")
          Res()
        }
        else checking(vdef.symbol) {
          apply(vdef.rhs, env2)
        }
      }
      env.add(vdef.symbol,  SymInfo(latentInfo = latentInfo))
    case vdef: ValDef if Analyzer.isNonParamField(vdef.symbol) =>
      env.add(vdef.symbol, SymInfo(assigned = false))
    case tdef: TypeDef if tdef.isClassDef  =>
      indexConstructors(tdef.symbol, tdef.rhs.asInstanceOf[Template], env)
    case _ =>
  }

  def checkAssign(lhs: Tree, rhs: Tree, env: Env)(implicit ctx: Context): Res = {
      val rhsRes = apply(rhs, env)
      if (rhsRes.hasErrors) return rhsRes

      def check(prefixRes: Res, sym: Symbol): Res = {
        if (prefixRes.hasErrors) return prefixRes
        if (prefixRes.state == State.Full) {
          if (!rhsRes.isFull)
            return Res(effects = Vector(Generic("Cannot assign an object under initialization to a full object", rhs.pos)))
        }
        else if (prefixRes.state == State.Filled) {
          if (rhsRes.state < Analyzer.typeState(sym.info))
            return Res(effects = Vector(Generic("Cannot assign an object of a lower state to a field of higher state", rhs.pos)))
        }
        else { // assign to partial is fine
          if (prefixRes.isLatent) {
            val valInfo = ValueInfo(state = rhsRes.state, latentInfo = rhsRes.latentInfo)
            prefixRes.latentInfo.asObject.assign(sym, valInfo, env.heap)
          }
        }

        Res()
      }

      lhs match {
        case ident @ Ident(_) =>
          ident.tpe match {
            case tp @ TermRef(NoPrefix, _) =>
              if (env.contains(tp.symbol)) {
                env(tp.symbol) = SymInfo(assigned = true, state = rhsRes.state, latentInfo = rhsRes.latentInfo)
                Res()
              }
              else if (!rhsRes.isFull) // leak assign
                Res(effects = Vector(Generic("Cannot leak an object under initialization", rhs.pos)))
              else Res()
            case tp @ TermRef(prefix, _) =>
              val prefixRes = checkRef(prefix, env, rhs.pos)
              check(prefixRes, tp.symbol)
          }
        case sel @ Select(qual, _) =>
          val prefixRes = apply(qual, env)
          check(prefixRes, sel.symbol)
      }
  }

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

  def apply(tree: Tree, env: Env)(implicit ctx: Context): Res = trace("checking " + tree.show, env)(tree match {
    case tmpl: Template =>
      // TODO: check parents
      checkStats(tmpl.body, env)
    case vdef : ValDef if !vdef.symbol.is(Lazy) && !vdef.rhs.isEmpty =>
      checkValDef(vdef, env)
    case _: DefTree =>  // ignore other definitions
      Res()
    case Closure(_, meth, _) =>
      checkClosure(meth.symbol, tree, env)
    case tree: Ident if tree.symbol.isTerm =>
      checkRef(tree.tpe, env, tree.pos)
    case tree: This =>
      checkRef(tree.tpe, env, tree.pos)
    case tree: Super =>
      checkRef(tree.tpe, env, tree.pos)
    case tree: Select if tree.symbol.isTerm =>
      checkSelect(tree, env)
    case tree: If =>
      checkIf(tree, env)
    case tree @ NewEx(tref, init, argss) => // must before Apply
      checkNew(tree, tref, init, argss, env)
    case tree: Apply =>
      val (fn, targs, vargss) = decomposeCall(tree)
      checkApply(tree, fn, vargss, env)
    case tree @ Assign(lhs, rhs) =>
      checkAssign(lhs, rhs, env)
    case tree: Block =>
      checkBlock(tree, env)
    case Typed(expr, _) =>
      apply(expr, env)
    case _ =>
      Res()
  })
}