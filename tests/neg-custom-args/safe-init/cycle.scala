class Parent {
  val child = new Child(this)
  child.show   // error

  val name = "parent"

  def show = child.show
}

import scala.annotation.partial

class Child(parent: Parent @partial) {
  val name = "child"

  println(parent.name) // error

  def show = {
    println(parent.name)
    println(name)
  }
}