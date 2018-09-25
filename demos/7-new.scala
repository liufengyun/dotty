class Foo {
  val bar = new Bar(this)
  new bar.Inner            // error

  val name = "foo"
}

class Bar(val foo: Partial[Foo]) {

  class Inner {
    val len = foo.name
  }
}
