package dotty.tools.dotc
package transform

import core._
import MegaPhase._
import Contexts.Context
import StdNames._
import Names._
import NameKinds.DefaultGetterName
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
import Annotations._
import util.Positions._
import Constants.Constant
import collection.mutable

package object init {
  implicit class TypesOps(val tp: Type) extends AnyVal {
    def isIcy(implicit ctx: Context) = tp.dealiasKeepAnnots.hasAnnotation(defn.IcyAnnot)

    def isCold(implicit ctx: Context) = tp.dealiasKeepAnnots.hasAnnotation(defn.ColdAnnot)

    def isWarm(implicit ctx: Context) = tp.dealiasKeepAnnots.hasAnnotation(defn.WarmAnnot)

    def value(implicit ctx: Context) =
      if (isCold) ColdValue
      else if (isWarm) WarmValue()
      else HotValue
  }

  def calledSymsIn(anchor: Symbol)(implicit ctx: Context): List[Symbol] =
    anchor.self.annotations.collect {
      case Annotation.Call(sym) => sym
    }

  implicit class SymOps(val sym: Symbol) extends AnyVal {
    def isIcy(implicit ctx: Context) =
      sym.hasAnnotation(defn.IcyAnnot) || sym.info.isIcy

    def isCold(implicit ctx: Context) =
      sym.hasAnnotation(defn.ColdAnnot) || sym.info.isCold

    def isWarm(implicit ctx: Context) =
      sym.hasAnnotation(defn.WarmAnnot) || sym.info.isWarm

    def isHot(implicit ctx: Context) =
      value.isHot

    def isInit(implicit ctx: Context) = sym.hasAnnotation(defn.InitAnnot)

    def isEffectiveCold(implicit ctx: Context) =
      sym.isIcy || sym.isCold || sym.isCalledAbove(sym.owner.asClass)

    def isEffectiveInit(implicit ctx: Context) =
      !sym.isEffectiveCold &&
      (sym.isInit || sym.allOverriddenSymbols.exists(_.isInit))

    def isCalledIn(anchor: Symbol)(implicit ctx: Context): Boolean =
      calledSymsIn(anchor).exists(_ == sym) || sym.allOverriddenSymbols.exists(_.isCalledIn(anchor))

    def isCalledAbove(from: ClassSymbol)(implicit ctx: Context) =
      from.baseClasses.tail.exists(cls => sym.isCalledIn(cls))

    def isCalledOrAbove(from: ClassSymbol)(implicit ctx: Context) =
      from.baseClasses.exists(cls => sym.isCalledIn(cls))

    def isClassParam(implicit ctx: Context) = sym.is(ParamAccessor)

    def isOverrideClassParam(implicit ctx: Context) =
      sym.allOverriddenSymbols.exists(_.isClassParam)

    def isDefinedOn(cls: ClassSymbol)(implicit ctx: Context): Boolean =
      cls.isSubClass(sym.owner)

    def value(implicit ctx: Context) =
      if (isCold) ColdValue
      else if (isWarm) WarmValue()
      else HotValue

    def isConcreteField(implicit ctx: Context) =
      sym.isTerm && sym.is(AnyFlags, butNot = Deferred | Method | Local | Private)

    def isNonParamField(implicit ctx: Context) =
      sym.isTerm && sym.is(AnyFlags, butNot = Method | ParamAccessor | Lazy | Deferred)

    def ignorable(implicit ctx: Context): Boolean =
      sym.name.is(DefaultGetterName) ||
        sym.is(Flags.JavaDefined) ||
        (sym.owner.eq(defn.AnyClass) && sym.is(Flags.Final))

    // def isField(implicit ctx: Context) =
    //   sym.isTerm && sym.is(AnyFlags, butNot = Method | Lazy | Deferred)

    def annotate(tp: Type)(implicit ctx: Context) =
      sym.addAnnotation(Annotations.ConcreteAnnotation(tpd.New(tp, Nil)))

    def enclosedIn(inSym: Symbol)(implicit ctx: Context): Boolean =
      sym.exists && ((sym `eq` inSym) || sym.owner.enclosedIn(inSym))
  }

  implicit def setting2ctx(implicit s: Setting): Context = s.ctx
  implicit def showSetting2ctx(implicit s: ShowSetting): Context = s.ctx
}