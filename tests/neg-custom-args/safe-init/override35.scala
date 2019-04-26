class Foo {
  def f: Int = 50

  def g: Int = f
}

trait Bar {
  def g: Int
  val a = g      // error
}

class Qux extends Foo with Bar {
  private val x = 30
  override def f = x
}