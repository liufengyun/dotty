trait Foo {
  val name: String
  val message = "hello, " + name   // error
}

class Bar extends Foo {
  val name = "Jack"
}