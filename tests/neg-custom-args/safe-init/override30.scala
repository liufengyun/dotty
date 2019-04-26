class Foo {
  def f: Int = 50

  def g: Int = f
}

class Bar extends Foo {
  g                        // error
  f                        // error
}

class Qux extends Bar {
  val a = 30
  override def f = a
}