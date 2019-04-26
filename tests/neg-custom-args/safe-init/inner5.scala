class Foo {
  class B {
    foo(10)
  }

  new B         // error
  val a = 3

  def foo(x: Int) = a + x
}