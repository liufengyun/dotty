import scala.annotation.filled

trait NameInfo

abstract class NameKind {
  class Info extends NameInfo {
    val x = foo
  }
  def foo: Int
}

class ClassifiedNameKind extends NameKind {
  def foo: Int = info.hashCode
  class MyInfo extends Info
  val info: Info = new MyInfo
}
