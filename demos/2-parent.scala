import scala.annotation.filled

abstract class Parent(p: Partial[String]) {
  val x = "name"
  lazy val z = bar
  def foo = bar
  def bar: Int
}

class Child(o: Partial[String]) extends Parent(o) {
  val m = this.x
  this.foo          // error
  this.z            // error

  def bar = y.size

  val y = "hello"
}