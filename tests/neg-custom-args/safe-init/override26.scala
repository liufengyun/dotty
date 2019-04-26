abstract class Foo {
  val name: String = "Foo"

  def title: String
}

trait Bar { this: Foo =>
  val message = "hello, " + name

  println(title)                        // error: uses Qux.this.x
}

class Qux extends Foo with Bar {
  val x = "hello"
  def title = x
}
