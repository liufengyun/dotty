trait TA {
  val x = "world"
}

trait TB { this: TA =>
  val m = "hello" + x         // error
}

class Bar extends TB with TA
