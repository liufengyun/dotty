import scala.annotation.init

trait Foo {
  val x = "world"
  val y = foo(5)

  @init
  def foo(n: Int): String
}

trait Bar {
  val m = "hello"

  def foo(n: Int) =  m
}

class Qux extends Foo with Bar  // error: Bar.foo needs to be annotated with

trait Yun {           //  `C extends Yun with Foo` will create problem
  val m = "hello"

  @init def foo(n: Int) =  m    // error: concrete trait methods may not be @init
}


class Tao {
  val m = "hello"

  def msg = "can be overriden"

  def foo(n: Int) =  m + msg
}

class Zen extends Tao with Foo  // error: Tao.foo needs to be `@init`

class Lux {
  val m = "hello"

  def msg = "can be overriden"             // error

  @init def foo(n: Int) =  m + msg         // error
}

class Logos extends Lux with Foo  // ok