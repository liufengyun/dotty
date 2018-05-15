class Foo {
  val bar = new Bar(this)
  var x: bar.Inner = _   // ok, partial value as type prefix

  class Inner {
    val len = list.size
  }

  val list = List(1, 2, 3)

  x = null
}

import scala.annotation.partial

class Bar(val foo: Foo @partial) {
  val inner = new foo.Inner   // error

  class Inner {
    val x = new foo.Inner
    val len = x.len
  }
}