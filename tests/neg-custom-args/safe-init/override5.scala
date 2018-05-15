trait Foo {
  @scala.annotation.partial
  def name: String

  val message = "hello, " + name
}

class Bar extends Foo {
  val name = "Jack"              // error: partial cannot be implemented by val
}