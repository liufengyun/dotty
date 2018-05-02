class Foo {
  val x = "hello"
  val fun: Int => Int = n => n + list.size   // ok, but fun is partial because it captures the partial value `this`
  fun(5)                                     // error: select on partial value

  List(5, 9).map(n => n + list.size)         // error: closure is partial, but a full value expected

  val list = List(1, 2, 3)

  List(5, 9).map(n => n + list.size)         // ok, `this.list` already initialized
}