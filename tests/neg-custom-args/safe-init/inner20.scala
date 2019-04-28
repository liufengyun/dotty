class A {
  class O {
    val x = 10

    class B {
      val y = n
      def f: Int = n
    }
  }

  val n = 20
}

class B extends A {
  val o = new O
  println((new o.B).f)     // error
  override val n = 50
}