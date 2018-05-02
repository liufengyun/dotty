class Foo {
  val x = "hello"
  val inner = new Inner          // error: prefix is partial

  val bar = new Bar(this)        // error: bar is partial
  val inner2 = new bar.Inner

  val list = List(1, 2, 3)

  class Inner {
    val len = list.size
  }
}


class Bar(val foo: Foo) {      // if we declare `foo` to be partial, then A, B will be rejected

  val inner = new foo.Inner    // A: prefix is partial

  class Inner {
    val len = foo.list.size    // B: select on partial value
  }
}