import scala.collection.mutable

trait Foo {
  @scala.annotation.init
  class A

  class B {
    foo(10)
  }

  def foo(x: Int) = 5 + x
}

class Bar extends Foo {
  new A       // OK
  new B       // error

  override def foo(x: Int) = x + id
  val id = 100
}