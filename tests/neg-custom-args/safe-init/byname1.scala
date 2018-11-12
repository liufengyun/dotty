class LazyList[A]

object LazyList {
  implicit final class a[A](l: => LazyList[A] @unchecked) {
    def #:: [B >: A](elem: => B): LazyList[B] = ???
  }

  implicit final class b[A](l: => LazyList[A]) {
    def *:: [B >: A](elem: => B): LazyList[B] = ???
  }
}

import LazyList._

final class Test {
  val a: LazyList[Int] = 5 #:: b
  val b: LazyList[Int] = 10 #:: a

  val x: LazyList[Int] = 5 *:: y     // error
  val y: LazyList[Int] = 10 *:: x
}