trait Foo {
  @scala.annotation.partial
  def name: String

  def title: String
}

trait Bar { this: Foo =>
  val message = "hello, " + name        // TODO: this should be an error

  println(title)                        // error
}