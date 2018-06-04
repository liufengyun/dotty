trait Foo {
  @scala.annotation.init
  def name: String

  val message = "hello, " + name
}

class Bar extends Foo {
  val name = "Jack"              // error: init cannot be implemented by val
}