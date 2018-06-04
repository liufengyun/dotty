class Parent {
  val child = new Child(this)
  child.number = 5

  val name = "parent"
}

import scala.annotation.partial

class Child(parent: Parent @partial) {
  val name = "child"
  var number = 0

  println(parent.name) // error

  def show = {
    println(parent.name)
    println(name)
  }
}