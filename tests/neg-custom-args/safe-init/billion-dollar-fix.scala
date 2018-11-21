import scala.annotation._

object Bilion {
  type Late[T] = (implicit () => T) @cold

  class Security(dba: Late[DBA]) {
    def work(): Unit = ???
  }
  class DBA(s: Late[Security], gui: Late[GUI]) {
    def work(): Unit = ???
  }
  class SMS(s: Late[Security], dba: Late[DBA]) {
    def work(): Unit = ???
  }
  class GUI(s: Late[Security], sms: Late[SMS], dba: Late[DBA]) {
    def work(): Unit = ???
  }
}

import Bilion._

final class Billion1 {
  val s: Security = new Security(dba)
  val dba: DBA = new DBA(s, gui)

  s.work()    // error
  dba.work()  // error

  val sms: SMS = new SMS(s, dba)
  val gui: GUI = new GUI(s, sms, dba)

  s.work()    // ok
  dba.work()  // ok
  sms.work()  // ok
  gui.work()  // ok
}
