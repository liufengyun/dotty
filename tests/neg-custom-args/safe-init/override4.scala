import scala.collection.mutable

class Foo {
  private val map: mutable.Map[Int, String] = mutable.Map.empty

  def enter(k: Int, v: String) = map(k) = v
}

class Bar extends Foo {
  enter(1, "one")                // error
  enter(2, "two")                // error
}

class Bar2 extends Bar {
  val mymap: mutable.Map[Int, String] = mutable.Map.empty

  override def enter(k: Int, v: String) = {
    mymap(k) = v
  }
}
