trait Foo {
  val name: String                             // error: @init required
  val message = "hello, " + name               // error: name should not be used during initialization
}

class Bar extends Foo {
  val name = "Jack"
}