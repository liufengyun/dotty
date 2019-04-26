class A(a: Int) {
  a + 3
  def foo() = a * 2
}

class B extends A(3) {
  foo()
  a          // error
  val a = 3
}