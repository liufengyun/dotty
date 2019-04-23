package scala.annotation.internal

import scala.annotation.Annotation

/** An annotation to indicate usage of names in methods.
 *  E.g. if we have
 *
 *      class A {
 *        val x: Int = 5
 *        def f: Int = x
 *      }
 *
 *  Then the symbol `f` would carry the annotations `@Use[this.x]`.
 */
class Use[T] extends Annotation
