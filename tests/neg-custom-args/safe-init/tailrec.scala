class Foo {
  private def rec(x: Int): Int =
    if (x == 0) 1
    else rec(x - 1)

  def f(): Int = g()
  def g(): Int = h()
  def h(): Int = f() + n

  f()  // error

  val n = rec(5)
}