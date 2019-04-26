class Foo {
  new this.Inner           // error, as Inner access `this.list`

  val list = List(1, 2, 3)

  val inner: Inner = new this.Inner // ok, `list` is instantiated
  lib.escape(inner)                 // ok, `inner` is fully initialized

  val name = "good"

  class Inner {
    val len = list.size
  }
}

object lib {
  def escape(x: Foo#Inner): Unit = ???
}
