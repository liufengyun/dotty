abstract class Parent extends Product {
  val a = productArity           // error
  val b = g                      // error

  def g: Int = productArity
}

case class Child(x: Int) extends Parent {
  val m = 10
  def productArity: Int = m
}