class A { self : B =>
  val y = f             // error
}

trait B(x: Int) {
   def f: Int = x
}

class C extends A with B(20)
