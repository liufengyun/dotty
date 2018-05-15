import scala.annotation.partial

trait Foo {
  val x = "world"
  foo(5)                       // error

  def foo(n: Int): String      // error: `@partial` needed
}


trait Bar {
  val x = "world"
  foo(5)

  @partial
  def foo(n: Int): String
}
