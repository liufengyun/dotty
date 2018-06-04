trait Foo {
  @scala.annotation.init
  def name: String

  def title: String
}

trait Bar { this: Foo =>
  val message = "hello, " + name        // ok

  println(title)                        // error
}