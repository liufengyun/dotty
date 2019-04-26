trait Foo {
  def getName: String

  def getTitle: String

  val message = "hello, " + getTitle + " " + getName   // error
}

class Bar(val name: String) extends Foo {
  val title = "Mr."

  def getName = name                 // ok: name is a Param field

  def getTitle = title
}

object Test {
  def main(args: Array[String]): Unit = {
    new Bar("Jack")
  }
}
