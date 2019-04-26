class A {
  object O {
    class B {
      val a = y
    }
    class C
  }

  class Inner {
    def f(n: String) = new O.C
  }

  println(new Inner)  // error
  println(new O.B)    // error

  val y = 10
}