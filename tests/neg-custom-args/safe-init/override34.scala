abstract class Foo {
  def name: String

  val message = "hello, " + name    // error
}

trait Bar {
  val name: String = "Foo"
}

class Qux extends Foo with Bar {
  val x = "hello"
}
