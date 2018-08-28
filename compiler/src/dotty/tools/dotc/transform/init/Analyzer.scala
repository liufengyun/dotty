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
}

object Rules {
  def latentState(latentValue: LatentValue, heap: Heap, pos: Position): State = latentValue match {
    case mtLatent: MethodInfo =>
      val res = latentValue.asMethod(i => ValueInfo(), heap.clone)
      if (res.hasErrors) State.Filled
      else if (res.isLatent) latentState(res.latentValue, heap, pos)
      else State.Full  // even if the result is partial, as the closure cannot be called
    case objLatent: ObjectValue =>
      State.Filled
    case NoLatent => ???  // impossible
  }

  // TODO: handle order to resolution
  def resolveParent(obj: ObjectRep, sym: Symbol)(implicit ctx: Context): Res = {
    debug(s"resolving $sym on ${obj.classSymbol}")
    debug(obj.toString)
    var res: Res = null
    obj.classSymbol.classParents.foreach { parentTp =>
      val cls = parentTp.classSymbol
      if (parentTp.member(sym.name).exists) {
        val info = obj(cls)

        if (res == null || info.isLatent)
          res = Res(state = info.state, latentValue = info.latentValue)
      }
    }

    if (res != null) res
    else if (sym.isConstructor) Res() // constructors are handled specially, see `checkNew`
    else if (obj.classSymbol.info.memberInfo(sym).exists) { // self annotation
      // TODO: possibility to refine based on `sym.owner` is class or trait
      Res(state = State.Partial)
    }
    else {
      debug(obj.toString)
      throw new Exception(s"Can't resolve $sym on class ${obj.classSymbol}")
    }
  }

  def init(outer: ObjectRep, sym: ClassSymbol, constr: Symbol, valueInfos: List[ValueInfo], heap: Heap, obj: ObjectRep, pos: Position, env: Env): Res = {
    val (tmpl: Template, envId) = outer.classEnv(sym.owner).getTree(cls)
    val clsEnv = env.heap(envId)

    // setup this
    val thisInfo =  new AtomObjectValue(obj.id)
    clsEnv.add(cls, SymInfo(state = State.Partial, latentValue = thisInfo))

    // setup outer this
    val outerInfo =  new AtomObjectValue(outer.id)
    clsEnv.add(cls, SymInfo(latentValue = outerInfo))

    // setup constructor params
    tmpl.constr.vparamss.flatten.zipWithIndex.foreach { case (param: ValDef, index: Int) =>
      val valInfo = valueInfos(index)
      clsEnv.add(param.symbol, SymInfo(assigned = true, state = valInfo.state, latentValue = valInfo.latentValue))
    }

    checkTemplate(cls, obj.tp, tmpl, heap(clsEnv.id), obj)
  }

  def assign(obj: ObjectRep, sym: Symbol, valInfo: ValueInfo, pos: Position)(implicit ctx: Context): Res =
    if (obj.contains(sym)) {
      obj(sym) = SymInfo(
        assigned = true,
        state = valInfo.state,
        latentValue = valInfo.latentValue
      )
      Res()
    }
    else {
      val parentRes = Rules.resolveParent(obj, sym)
      assign(parentRes, sym, valInfo, obj.heap, pos)
    }

  def assign(prefixRes: Res, sym: Symbol, valueInfo: ValueInfo, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    if (prefixRes.hasErrors) return prefixRes
    if (prefixRes.isFull) assignFull(sym, valueInfo, pos)
    else if (prefixRes.isFilled) assignFilled(sym, valueInfo, pos)
    else assignPartial(prefixRes.latentValue, sym, valueInfo, heap, pos)
  }

  def assignPartial(obj: LatentValue, sym: Symbol, valueInfo: ValueInfo, heap: Heap, pos: Position)(implicit ctx: Context): Res =
    if (obj != NoLatent)
      obj.asObject.assign(sym, valueInfo, heap, pos)
    else Res() // TODO: assign to partial is fine?

  def assignFilled(sym: Symbol, valueInfo: ValueInfo, pos: Position)(implicit ctx: Context): Res = {
    if (valueInfo.state < Analyzer.typeState(sym.info))
      return Res(effects = Vector(Generic("Cannot assign an object of a lower state to a field of higher state", pos)))
    // TODO: latent
    Res()
  }

  /** Assign to a local variable, i.e. TermRef with NoPrefix */
  def assignLocal(env: Env, sym: Symbol, valueInfo: ValueInfo, pos: Position)(implicit ctx: Context): Res =
    if (env.contains(sym)) {
      env(sym) = SymInfo(assigned = true, state = valueInfo.state, latentValue = valueInfo.latentValue)
      Res()
    }
    else if (!valueInfo.isFull) // leak assign
      Res(effects = Vector(Generic("Cannot leak an object under initialization", pos)))
    else Res()

  def assignFull(sym: Symbol, valueInfo: ValueInfo, pos: Position)(implicit ctx: Context): Res =
    if (!valueInfo.isFull)
      Res(effects = Vector(Generic("Cannot assign an object under initialization to a full object", pos)))
    else Res()

  def select(obj: ObjectRep, sym: Symbol, pos: Position, static: Boolean = false)(implicit ctx: Context): Res =
    if (obj.contains(sym)) {
      if (static) Rules.selectStatic(obj, sym, pos)
      else Rules.selectDynamic(obj, sym, pos)
    }
    else {
      val parentRes = Rules.resolveParent(obj, sym)
      Rules.select(parentRes, sym, obj.heap, pos)
    }

  def selectDynamic(env: ObjectRep, sym: Symbol, pos: Position)(implicit ctx: Context): Res = {
    debug("select dynamic-dispatch symbol " + sym)
    if (sym.is(Lazy)) selectLazy(env, sym, pos)
    else if (sym.is(Method)) {
      val res = selectMethod(env, sym, pos)

      if (!sym.hasAnnotation(defn.PartialAnnot) && !sym.isEffectivelyFinal)
        res += OverrideRisk(sym, pos)

      res
    }
    else if (sym.isClass) selectClass(env, sym, pos)
    else {
      val res = selectField(env, sym, pos)

      if (sym.is(Deferred) && !sym.hasAnnotation(defn.InitAnnot))
        res += UseAbstractDef(sym, pos)

      res
    }
  }

  def selectStatic(env: ObjectRep, sym: Symbol, pos: Position)(implicit ctx: Context): Res = {
    debug("select static-dispatch symbol " + sym)
    if (sym.is(Lazy)) selectLazy(env, sym, pos)
    else if (sym.is(Method)) selectMethod(env, sym, pos)
    else if (sym.isClass) selectClass(env, sym, pos)
    else selectField(env, sym, pos)
  }

  def selectClass(env: Env, sym: Symbol, pos: Position): Res =
    Res(latentValue = env(sym).latentValue)

  def selectField(env: Env, sym: Symbol, pos: Position): Res = {
    val symInfo = env(sym)

    var effs = Vector.empty[Effect]
    if (!env.isAssigned(sym)) effs = effs :+ Uninit(sym, pos)

    Res(effects = effs, state = symInfo.state, latentValue = symInfo.latentValue)
  }

  def selectMethod(env: Env, sym: Symbol, pos: Position)(implicit ctx: Context): Res = {
    val symInfo = env(sym)
    if (sym.info.isInstanceOf[ExprType]) {       // parameter-less call
      val latentValue = symInfo.latentValue.asMethod
      val res2 = latentValue(i => null, env.heap)

      if (res2.effects.nonEmpty)
        res2.effects = Vector(Call(sym, res2.effects, pos))

      res2
    }
    else Res(latentValue = symInfo.latentValue)
  }

  def selectLazy(env: Env, sym: Symbol, pos: Position): Res = {
    val symInfo = env(sym)
    if (!symInfo.forced) {
      val res = symInfo.latentValue.asMethod.apply(i => null, env.heap)
      env(sym) = symInfo.copy(forced = true, state = res.state, latentValue = res.latentValue)

      if (res.hasErrors) Res(effects = Vector(Force(sym, res.effects, pos)))
      else Res(state = res.state, latentValue = res.latentValue)
    }
    else Res(state = symInfo.state, latentValue = symInfo.latentValue)
  }

  def select(res: Res, sym: Symbol, heap: Heap, pos: Position)(implicit ctx: Context): Res = {
    debug(s"select symbol $sym on " + res)

    if (res.hasErrors) res
    else if (res.isLatent) {
      if (res.latentValue.isObject) res.latentValue.asObject.select(sym, heap, pos)
      else {
        assert(sym.name.toString == "apply")
        Res(latentValue = res.latentValue, effects = res.effects) // closures
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
          if (!Analyzer.isPartial(sym) && !Analyzer.isFilled(sym))
            res += Generic(s"The $sym should be marked as `@partial` or `@filled` in order to be called", pos)

          Res(state = State.Full, effects = res.effects)
        }
        else if (sym.is(Lazy)) {
          if (!Analyzer.isPartial(sym) && !Analyzer.isFilled(sym))
            res += Generic(s"The lazy field $sym should be marked as `@partial` or `@filled` in order to be accessed", pos)

          Res(state = Analyzer.typeState(sym.info), effects = res.effects)
        }
        else if (sym.isClass) {
          if (!Analyzer.isPartial(sym) && !Analyzer.isFilled(sym))
            res += Generic(s"The nested $sym should be marked as `@partial` or `@filled` in order to be instantiated", pos)

          Res(effects = res.effects)
        }
        else {
          Res(state = Analyzer.typeState(sym.info), effects = res.effects)
        }
      }
      else Res()
    }
  }

  /** Select a local variable, i.e. TermRef with NoPrefix */
  def selectLocal(env: Env, sym: Symbol, pos: Position)(implicit ctx: Context): Res =
    if (env.contains(sym)) {
      if (sym.is(Lazy)) Rules.selectLazy(env, sym, pos)
      else if (sym.is(Method)) Rules.selectMethod(env, sym, pos)
      else Rules.selectField(env, sym, pos)
    }
    else Res()
}

object Indexing {
  /** Index local definitions */
  def indexStats(stats: List[Tree], env: Env)(implicit ctx: Context): Unit = stats.foreach {
    case ddef: DefDef =>
      env.addTree(ddef.symbol, ddef)
    case vdef: ValDef if vdef.symbol.is(Lazy)  =>
      env.addTree(vdef.symbol,  vdef)
    case tdef: TypeDef if tdef.isClassDef  =>
      env.addTree(tdef.symbol, tdef.rhs)
    case _ =>
  }

  def indexTemplate(cls: ClassSymbol, tp: Type, tmpl: Template, env: Env, obj: ObjectRep): ObjectValue = {
    // index current class environment
    val innerEnv = env.fresh()
    indexStats(tmpl.body, innerEnv)
    obj.add(ClassEnv(innerEnv.id, tp))

    // index parent class environments
    val atom = new AtomObjectValue(obj.id)
    cls.baseClasses.tail.foldLeft(atom) { (parent, acc) =>
      val baseType = tp.baseType(parent)
      indexClass(parent, baseType, env, obj).join(acc)
    }
  }

  def indexClass(cls: ClassSymbol, tp: Type, env: Env, obj: ObjectRep)(implicit ctx: Context): ObjectValue = {
    def toPrefix(tp: Type): TypeRef = tp match {
      case AppliedType(tycon, _) => toPrefix(tycon.dealias)
      case tp: TypeRef => tp.prefix
    }

    def default = new AtomObjectValue(obj.id)

    val prefix = toPrefix(tp)
    if (prefix == NoPrefix) {
      // must exist in scope
      val (tmpl: Template, envId) = env.getTree(cls)
      val envOuter = env.heap(envId).asInstanceOf[Env]

      val innerEnv = envOuter.fresh()
      indexStats(tmpl.body, innerEnv)
      obj.add(ClassEnv(innerEnv.id, tp))
    }
    else {
      val prefixRes = checkRef(prefix, env, parent.pos)
      if (prefixRes.isLatent)
        prefixRes.latentValue.asObject.index(cls, tp, obj)
      else default
    }
  }

  def indexInnerClass(cls: ClassSymbol, tp: Type, inner: ObjectRep, outer: ObjectRep)(implicit ctx: Context): ObjectValue = {
    val enclosingCls = cls.owner
    if (outer.classEnv.contains(enclosingCls)) {
      val ClassEnv(envId, _) = outer.classEnv(enclosingCls)
      val env = outer.heap(envId)
      val (tmpl: Template, _) = env.getTree(cls)

      // don't go recursively for parents as indexing is based on linearization
      val innerEnv = env.fresh()
      indexStats(tmpl.body, innerEnv)
      inner.add(ClassEnv(innerEnv.id, tp))
    }
    else new AtomObjectValue(obj.id)
  }

  def initObject(cls: ClassSymbol, tmpl: Template, obj: ObjectRep)(implicit ctx: Context): Unit = {
    cls.typeRef.fields.foreach { field =>
      obj.add(field.symbol.name, SymInfo(assigned = false))
    }

    // primary constructor fields are init early
    tmpl.constr.vparamss.flatten.foreach { (param: ValDef) =>
      val sym = cls.info.member(param.name).suchThat(x => !x.is(Method)).symbol
      obj(sym) = SymInfo(assigned = true, state = Analyzer.typeState(sym.info))
    }
  }

  def indexOuter(cls: ClassSymbol, env: Env)(implicit ctx: Context) = {
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

  def checkParams(sym: Symbol, valInfos: List[ValueInfo], paramInfos: List[Type], env: Env, positions: List[Position])(implicit ctx: Context): Res = {
    def paramState(index: Int) = Analyzer.typeState(paramInfos(index))

    valInfos.zipWithIndex.foreach { case (valInfo, index) =>
      if (valInfo.state < paramState(index))
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

    if (funRes.isLatent) {
      val valInfos = args.map { arg =>
        val res = apply(arg, env)
        effs = effs ++ res.effects
        res.valueInfo
      }

      if (effs.size > 0) return Res(effects = effs)

      indentedDebug(s">>> calling $funSym")
      val res = funRes.latentValue.asMethod(valInfos, env.heap)
      if (res.hasErrors) res.effects = Vector(Latent(tree, res.effects))
      res
    }
    else {
      val valInfos = args.map { arg =>
        val res = apply(arg, env)
        effs = effs ++ res.effects

        if (res.isLatent)
          res.state = Rules.latentState(res.latentValue, env.heap, arg.pos)

        res.valueInfo
      }

      if (effs.size > 0) return Res(effects = effs)

      checkParams(funSym, valInfos, paramInfos, env, args.map(_.pos))
    }
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
      Rules.selectLocal(env, tp.symbol, pos)
    case tp @ TermRef(prefix, _) =>
      val res = checkRef(prefix, env, pos)
      Rules.select(res, tp.symbol, env.heap, pos)
    case tp @ ThisType(tref) =>
      val cls = tref.symbol
      if (cls.is(Package)) Res() // Dotty represents package path by ThisType
      else {
        val symInfo = env(cls)
        Res(latentValue = symInfo.latentValue, state = symInfo.state)
      }
    case tp @ SuperType(thistpe, supertpe) =>
      // TODO : handle `supertpe`
      checkRef(thistpe, env, pos)
  }

  def checkClosure(sym: Symbol, tree: Tree, env: Env)(implicit ctx: Context): Res =
    Res(latentValue = env(sym).latentValue)

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
    val sym = vdef.symbol

    // take `_` as uninitialized, otherwise it's initialized
    if (!tpd.isWildcardArg(vdef.rhs)) sym.termRef match {
      case tp @ TermRef(NoPrefix, _) =>
        Rules.assignLocal(env, tp.symbol, rhsRes.valueInfo, vdef.rhs.pos)
      case tp @ TermRef(prefix, _) =>
        val prefixRes = checkRef(prefix, env, vdef.rhs.pos)
        assert(!prefixRes.hasErrors)
        prefixRes.latentValue.asObject.assign(sym, rhsRes.valueInfo, env.heap, vdef.pos)
    }

    Res(effects = rhsRes.effects)
  }

  def checkStats(stats: List[Tree], env: Env)(implicit ctx: Context): Res =
    stats.foldLeft(Res()) { (acc, stat) =>
      indentedDebug(s"acc = ${pad(acc.toString)}")
      val res1 = apply(stat, env)
      acc.copy(effects = acc.effects ++ res1.effects)
    }

  def checkBlock(tree: Block, env: Env)(implicit ctx: Context): Res = {
    val newEnv = env.fresh()
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

  def checkAssign(lhs: Tree, rhs: Tree, env: Env)(implicit ctx: Context): Res = {
    val rhsRes = apply(rhs, env)
    if (rhsRes.hasErrors) return rhsRes

    lhs match {
      case ident @ Ident(_) =>
        ident.tpe match {
          case tp @ TermRef(NoPrefix, _) =>
            Rules.assignLocal(env, tp.symbol, rhsRes.valueInfo, rhs.pos)
          case tp @ TermRef(prefix, _) =>
            val prefixRes = checkRef(prefix, env, rhs.pos)
            Rules.assign(prefixRes, tp.symbol, rhsRes.valueInfo, env.heap, rhs.pos)
        }
      case sel @ Select(qual, _) =>
        val prefixRes = apply(qual, env)
        Rules.assign(prefixRes, sel.symbol, rhsRes.valueInfo, env.heap, rhs.pos)
    }
  }

  def checkParents(cls: ClassSymbol, parents: List[Tree], env: Env, obj: ObjectValue)(implicit ctx: Context): Res = {
    val baseClasses = cls.baseClasses.tail
    val parentsOrdered = baseClasses.map(p => parents.find(_.tpe.classSymbol `eq` p)).collect {
      case Some(parent) => parent
    }

    val covered = mutable.Set.empty[Symbo]

    parentsOrdered.foldLeft(Res()) { (acc, parent) =>
      parent match {
        case tree @ NewEx(tref, init, argss) =>
          // TODO: not all of them
          covered ++= tref.classSymbol.baseClasses
          val res = checkInit(tref, init, argss, env, obj)
          acc.copy(effects = acc.effects ++ res.effects)
        case _ =>

          Res()
      }
    }
  }

  def checkNew(tree: Tree, tref: TypeRef, init: TermRef, argss: List[List[Tree]], env: Env)implicit ctx: Context): Res = {
    val cls = tref.classSymbol
    val args = argss.flatten

    val prefixRes = checkRef(tref.prefix, env, parent.pos)
    if (prefixRes.isLatent) { // env may not contain `cls`, but prefixRes should
      // setup constructor params
      var effs = Vector.empty[Effect]
      val valInfos = args.map { arg =>
        val res = apply(arg, env)
        effs = effs ++ res.effects
        res.valueInfo
      }

      val obj = env.newObject

      // index parent class environments
      val atom = new AtomObjectValue(obj.id)
      cls.baseClasses.tail.foldLeft(atom) { (parent, acc) =>
        val baseType = tree.tpe.baseType(parent)
        indexClass(parent, baseType, env, obj).join(acc)
      }

      // index current class
      prefixRes.latentValue.asObject.index(cls, tree.tp, obj)

      prefixRes.latentValue.asObject.init(cls, initsymbol, valInfos, env.heap, obj, tree.pos)
    }
    else { // type checking
      val clsRes = Rules.select(prefixRes, cls, env.heap, parent.pos)
      if (clsRes.hasErrors) return clsRes

      val paramInfos = init.widen.paramInfoss.flatten

      // check params
      var effs = Vector.empty[Effect]
      val valInfos = args.map { arg =>
        val res = apply(arg, env)
        effs = effs ++ res.effects

        if (res.isLatent)
          res.state = Rules.latentState(res.latentValue, env.heap, arg.pos)

        res.valueInfo
      }

      if (effs.size > 0) return Res(effects = effs)

      val paramRes = checkParams(cls, valInfos, paramInfos, env, args.map(_.pos))
      if (paramRes.hasErrors) return paramRes

      if (!prefixRes.isFull || valInfos.exists(v => !v.isFull)) Res(state = State.Filled)
      else Res(state = State.Full)
    }
  }

  def checkInit(tree: Tree, tref: TypeRef, init: TermRef, argss: List[List[Tree]], env: Env, obj: ObjectRep)implicit ctx: Context): Res = {
    val cls = tref.classSymbol
    val args = argss.flatten

    val prefixRes = checkRef(tref.prefix, env, parent.pos)
    if (prefixRes.isLatent) { // env may not contain `cls`, but prefixRes should
      // setup constructor params
      var effs = Vector.empty[Effect]
      val valInfos = args.map { arg =>
        val res = apply(arg, env)
        effs = effs ++ res.effects
        res.valueInfo
      }

      prefixRes.latentValue.asObject.init(cls, init.symbol, valInfos, env.heap, obj, tree.pos)
    }
    else { // type checking
      val clsRes = Rules.select(prefixRes, cls, env.heap, parent.pos)
      if (clsRes.hasErrors) return clsRes

      val paramInfos = init.widen.paramInfoss.flatten

      // check params
      var effs = Vector.empty[Effect]
      val valInfos = args.map { arg =>
        val res = apply(arg, env)
        effs = effs ++ res.effects

        if (res.isLatent)
          res.state = Rules.latentState(res.latentValue, env.heap, arg.pos)

        res.valueInfo
      }

      if (effs.size > 0) return Res(effects = effs)

      val paramRes = checkParams(cls, valInfos, paramInfos, env, args.map(_.pos))
      if (paramRes.hasErrors) return paramRes

      if (!prefixRes.isFull || valInfos.exists(v => !v.isFull)) Res(state = State.Filled)
      else Res(state = State.Full)
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

  def checkTemplate(cls: ClassSymbol, tp: Type, tmpl: Template, env: Env, obj: ObjectRep)(implicit ctx: Context) = {
    checkParents(tmpl.parents, env, obj).join(checkStats(tmpl.body, env))
  }

  def apply(tree: Tree, env: Env)(implicit ctx: Context): Res = trace("checking " + tree.show, env)(tree match {
    case vdef : ValDef if !vdef.symbol.is(Lazy) && !vdef.rhs.isEmpty =>
      checkValDef(vdef, env)
    case _: DefTree =>  // ignore, definitions, already indexed
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