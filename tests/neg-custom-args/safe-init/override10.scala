trait Foo {
  def f: () => String = () => message
  def message: String
}

class Bar extends Foo {
  f()                        // error
  val message = "hello"
}