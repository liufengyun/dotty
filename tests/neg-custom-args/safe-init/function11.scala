final class Capture {
  private[this] var m: Boolean = false

  (0 to 10).foreach { i =>    // error
    f()
  }

  val a = 10

  def f() = do {
    println(a)
  } while(m)
}

final class Capture2 {
  private[this] var m: Boolean = false

  (0 to 10).foreach { i =>
    f()
  }

  val a = 10

  def f() = do {
    m = false
  } while(m)

  (0 to 10).foreach { i =>
    f()
  }
}