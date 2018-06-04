class Foo {
  val name = "child"

  println(show)                // error

  def show = println(name)     // error
}


final class Bar {
  val name = "child"

  println(show)

  def show = println(name)
}
