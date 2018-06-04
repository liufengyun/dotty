class X {
  object A {
    name.size
    def foo: Int = name.size
    def bar: Int = 10
  }

  A.foo                              // error
  A.bar

  val name = "jack"
}


class Y {
  class A {
    name.size
    def foo: Int = name.size
    def bar: Int = 10
  }

  (new A).foo                        // error
  (new A).bar                        // error

  val name = "jack"
}