class A {
  def f: Int = 10
}

class B extends A {
  this.getClass // ok, java method
  f // error
}