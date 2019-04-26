trait Foo(x: Int) {
  def name: String = "hello"

  def f: Int = x
}

trait Bar { this: Foo =>
  val title   = "Mr."
  val message = "hello, " + name

  println(title)

  println(f)       // error: from Qux2
}

class Qux extends Bar with Foo(3)
class Qux2 extends Foo(3) with Bar