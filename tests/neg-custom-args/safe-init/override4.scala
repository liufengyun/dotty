import scala.annotation.init
import scala.collection.mutable

trait Foo {
  val map: mutable.Map[Int, String] = mutable.Map.empty

  @init
  def enter(k: Int, v: String) = map(k) = v
}

class Bar extends Foo {
  enter(1, "one")
  enter(2, "two")
}

class Bar2 extends Bar {
  val mymap: mutable.Map[Int, String] = mutable.Map.empty

  def enter(k: Int, v: String) = {
    mymap(k) = v
  }
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