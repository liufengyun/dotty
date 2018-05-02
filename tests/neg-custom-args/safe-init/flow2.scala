class Foo {
  val len  = list.size     // error
  val list = List(4, 6)

  lazy val len2 = list.size  // ok
  val list = List(4, 6)

}