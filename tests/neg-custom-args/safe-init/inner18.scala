class A {
  def foo(g: () => Int) = {
    class B {
      def m: Int = g() + a
      lazy val b = new B
    }

    new B
  }

  final def bar() = {
    class B {
      def m: Int = 100
      lazy val b = new B
    }

    new B
  }

  println(foo(() => f))    // error
  println(bar())

  def f: Int = 10
  val a = 10
}