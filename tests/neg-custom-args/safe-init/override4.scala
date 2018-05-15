import scala.annotation.init
import scala.collection.mutable

trait Foo {
  val map: mutable.Map[Int, String] = mutable.Map.empty

  @init
  final def enter(k: Int, v: String) = map(k) = v
}

class Bar extends Foo {
  enter(1, "one")
  enter(2, "two")
}

trait Foo1 {
  val map: mutable.Map[Int, String] = mutable.Map.empty

  @init
  def enter(k: Int, v: String) = map(k) = v  // error: init methods need to be final
}


trait Foo2 {
  def map: mutable.Map[Int, String]

  @init
  def enter(k: Int, v: String) = map(k) = v  // error: init methods cannot access `map`
}