sealed trait Foo
final case class Bar[A](a: A) extends Foo

def test(x: Foo) = x match {
  case Bar(a: Int) =>
}
