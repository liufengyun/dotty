final class Foo {
  def fun: Int => Int = n => n + x.size
  fun(5)                                          // error: select on cold value

  val x = "hello"
}