class Parent {
  def foo(): Int = 5
}

class Child extends Parent {
  val a = 4

  def g() = foo()
  g() + b  // error

  val b = 10
  g()
}