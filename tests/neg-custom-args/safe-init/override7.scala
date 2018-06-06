import scala.annotation.init

trait Foo {
  @init
  def getName: String

  @init
  def getTitle: String

  val message = "hello, " + getTitle + " " + getName
}

class Bar(val name: String) extends Foo {
  val title = "Mr."

  @init
  def getName = name                 // ok: name is a Param field

  @init
  def getTitle = title               // error: title cannot use title
}

object Test {
  def main(args: Array[String]): Unit = {
    new Bar("Jack")
  }
}

trait Dao(val name: String) extends Foo {
  val title = "Mr."

  @init
  def getName = name          // error: cannot access `name`
}

trait Zen(val name: String) {
  val title = "Mr."

  @init
  def getName = name          // error: cannot access `name`
}