import scala.annotation.init

trait Foo {
  val x = "world"
  foo(5)

  private def foo(n: Int): String = x + n
}

class Bar extends Foo {
  val y = "hello"

  foo(5)                       // error

  def foo(n: Int): String = {  // error: need to be private or final
    println("in foo")
    println(y.size)
    y + x
  }
}
