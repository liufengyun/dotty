class Foo {
  val list = List(4, 6)
  val len  = list.size     // standard typing: list is `unclassified`, this line invalid
                           // flow-sensitive typing + commit-only fields: allowed

  def foo(x: String | Null): String =
    if (x == null) "hello" // generalize to `isInstanceOf`
    else x
}