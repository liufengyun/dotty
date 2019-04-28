object Foo {
  val self = this
  val x = self.n    // error
  val n = 10
}