import scala.collection.mutable
import scala.annotation.filled

class Foo {
  val map: mutable.Map[Int, String] = mutable.Map.empty

  def enter(k: Int, v: String) = map(k) = v
}

class Bar extends Foo {
  enter(1, "one")
  enter(2, "two")
}