class Foo {
  def b = {
    name.size
    lazy val m = name.size
    def bar = name.size
    bar
    m
  }

  b    // error

  val name = "Jack"
}