object Flags {
  class Inner {
    println(b)            // error
  }

  new Flags.Inner         // error

  val a = Flags.b + 3     // error
  val b = 5
}

object Flags2 {
  class Inner {
    println(b)
  }


  lazy val a = 3
  val b = 5
}
