trait Foo {
  println("init x")
  val x = "world"
  foo(5)

  def foo(n: Int): String      // error: `init` method should not be abstract
}

class Bar extends Foo {
  println("init y")
  val y = "hello"

  def foo(n: Int): String = {  // error: `init` method may not be overridden
    println("in foo")
    println(y.size)
    y + x
  }
}

object Test {
  def main(args: Array[String]): Unit = new Bar
}