class Foo {
  println("init x")
  val x = "world"
  foo(5)

  def foo(n: Int): String = {           // add `init` flag to method
    println(x.size)
    "hello " + x
  }
}

class Bar extends Foo {
  println("init y")
  val y = "hello"

  override def foo(n: Int): String = {    // error: init method may not be overriden
    println("in foo")
    println(y.size)
    y + x
  }
}

object Test {
  def main(args: Array[String]): Unit = new Bar
}