import scala.language.implicitConversions
import scala.annotation._

class LazyList[A] {
  def isEmpty: Boolean = true
  def head: A = ???
  def tail: LazyList[A] = ???
}

object LazyList {
  inline implicit def toHelper[A](l: => LazyList[A] @cold): Helper[A] = new Helper(l)
  final class Helper[A](l: => LazyList[A] @cold) {
    @init
    def #:: [B >: A](elem: => B @cold): LazyList[B] @warm = ???
  }

  implicit final class b[A](l: => LazyList[A]) {
    def *:: [B >: A](elem: => B): LazyList[B] = ???
  }
}

import LazyList._

final class Test1 {
  val a: LazyList[Int] = 5 #:: b
  a.head // error
  val b: LazyList[Int] = 10 #:: a

  a.head // ok
  b.head // ok

  val x: LazyList[Int] = 5 *:: y     // error
  val y: LazyList[Int] = 10 *:: x
}

final class Test2 {
  val a: LazyList[Int] = 5 #:: b
  a.head // error
  val b: LazyList[Int] = 10 #:: 30 #:: c

  a.head // error
  b.head // error

  val c: LazyList[Int] = 20 #:: a
}

final class Test3 {
  val a: LazyList[Int] = 5 #:: b
  val b: LazyList[Int] = 10 #:: 30 #:: c

  a.head // error
  b.head // error

  val c: LazyList[Int] = 20 #:: a

  a.head // ok
  b.head // ok
}