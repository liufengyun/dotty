abstract class Foo {
  def name: String
  def title: String

  val message = "hello, " + name     // error

  println(title)                     // error
}

trait Bar {
  val name: String = "Foo"

  def title: String = name
}

class Qux extends Foo with Bar {
  val x = "hello"
}
