object Flags {
  class Inner {
    println(b)
  }

  new Flags.Inner         // error
  val b = 5
}
