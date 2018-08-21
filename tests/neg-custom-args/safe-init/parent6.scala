trait Foo {
  @scala.annotation.filled
  class A

  class B {
    foo(10)
  }

  def foo(x: Int) = 5 + x
}

class Bar extends Foo {
  val a = new A         // OK
  val b = new B         // error

  override def foo(x: Int) = x + id
  val id = 100
}