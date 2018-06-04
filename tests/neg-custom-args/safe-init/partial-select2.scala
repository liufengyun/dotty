abstract class Parent {
  var number = 0

  def show: Unit
}

import scala.annotation.partial

class Child extends Parent {
  number = 0

  println(show)                // error

  def show = println(name)     // error  // error

  val name = "child"
}