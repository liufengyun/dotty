class Foo {
  val bar = new Bar(this)
  new bar.Inner            // error

  new this.Inner           // error, as Inner access `this.list`

  val list = List(1, 2, 3)

  val inner = new this.Inner // ok, `list` is instantiated

  val name = "good"

  class Inner {
    val len = list.size      // error: create new instance from line 5
  }
}

import scala.annotation.partial

class Bar(val foo: Foo @partial) {
  val inner = new foo.Inner   // error

  class Inner {
    val len = inner.len
  }
}