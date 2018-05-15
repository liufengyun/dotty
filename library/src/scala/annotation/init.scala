package scala.annotation

/** An annotation to indicate that an instance method may be called
 *  during instantiation of the instance.
 *
 *  Init methods are final, and they cannot be abstract.
 */
class init extends StaticAnnotation
