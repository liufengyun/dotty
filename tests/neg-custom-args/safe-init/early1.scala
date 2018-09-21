class Parent {
  def foo(): Int = 5
}

final class Child extends Parent {
  val a = 4

  def g() = foo()
  g()  // error

  val b = 10
  g()  // ok
}