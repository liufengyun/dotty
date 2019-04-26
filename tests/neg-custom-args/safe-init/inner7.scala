class Parent {
  class Inner1 {
    val len = foo
  }

  val list = List(3, 5, 6)
  def foo: Int = 5
}

class Child extends Parent {
  class InnerA extends Inner1

  new InnerA      // error
  override val list = List(4, 5)
  override def foo: Int = list.size
}
