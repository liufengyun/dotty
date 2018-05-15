import scala.annotation.partial

abstract class Parent(p: String @partial) {
  val x = "name"
  lazy val z = bar
  def foo = bar
  def bar: Int
}

class Child(o: String @partial) extends Parent(o) {
  val y = "hello"

  val m = this.x
  this.foo          // error
  this.z            // error

  def bar = y.size
}