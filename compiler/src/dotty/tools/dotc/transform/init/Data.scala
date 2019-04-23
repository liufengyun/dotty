package dotty.tools.dotc
package transform
package init

import core._
import MegaPhase._
import Contexts.Context
import StdNames._
import Names._
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


/** The result of analyzing an expression
 *
 *  @param actual the actual effects
 *  @param latent the latent effects of a function or inner class instance
 *
 *  Effects as follows:
 *
 *    - `C.this`: leak of this
 *    - `C.this.f`: field access, possibly dynamic (if `f` is not `private` or `final`)
 *    - `C.this.m`: method call, possibly dynamic
 *    - `C.super.m`: method call, possibly dynamic
 *    - `C.super[D].m`: method call, possibly dynamic
 *    - `C.this.D`: inner class instantiation
 *
 *  If modular analysis:
 *
 *    - `C.this.D.<init>`: constructor call, only used as effects of constructors
 *
 */
case class Res(actual: Set[Type] = Set.empty, latent: Set[Type] = Set.empty)
