class Foo(val foo1: Foo) {
  class Inner {
    val len = name.size
  }

  new this.Inner  // error
  new foo1.Inner

  val name = "hello"
}
