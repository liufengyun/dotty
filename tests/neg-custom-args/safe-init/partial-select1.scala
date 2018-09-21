class Parent {
  val child = new Child(this)
  child.number = 5

  val name = "parent"
}

class Child(parent: Partial[Parent]) {
  val name = "child"
  var number = 0

  println(parent.name) // error

  def show = {
    println(parent.name)
    println(name)
  }
}