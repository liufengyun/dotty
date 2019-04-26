trait Foo {
  def name: String

  val message = "hello, " + name   // error
}

class Bar extends Foo {
  val name = "Jack"
}


trait Zen {
  val name: String

  val message = "hello, " + name   // error
}

class Tao extends Zen {
  val name = "Jack"
}


trait Base {
  val name: String

  val message = "hello, " + name   // error
}

class Derived(val name: String) extends Base

class Derived2 extends Derived("hello") {
  override val name: String = "ok"
}
