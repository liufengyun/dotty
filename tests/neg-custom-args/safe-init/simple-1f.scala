import scala.annotation.partial

class Foo(x: String @partial) {
  var name: String = _
  name.size    // error

  name = "hello, world"
  name.size

  val y = name
  y.size

  name = x   // error
}

class Bar(x: String @partial) {
  var name: String = x
  name.size    // error

  name = "hello, world"
  name.size

  name = x   // error
}