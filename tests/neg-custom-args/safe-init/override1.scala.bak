import scala.annotation.init

trait Foo {
  val x = "world"
  foo(5)                       // error

  def foo(n: Int): String      // error: `@init` needed
}


trait Bar {
  val x = "world"
  foo(5)

  @init
  def foo(n: Int): String
}
