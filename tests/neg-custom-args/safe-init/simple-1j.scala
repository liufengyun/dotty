object Flags {
  @scala.annotation.init
  case class FlagSet(val bits: Long) {
    println(JavaStaticTerm)                        // error
    def toTermFlags = if (bits == 0) this else FlagSet(bits & ~KINDFLAGS | TERMS)
  }

  private val flagName = Array.fill(64, 2)("")

  private final val TERMindex = 0
  private final val TYPEindex = 1
  private final val TERMS = 1 << TERMindex
  private final val TYPES = 1 << TYPEindex
  private final val KINDFLAGS = TERMS | TYPES

  private def commonFlag(index: Int, name: String): FlagSet = {
    flagName(index)(TERMindex) = name
    flagName(index)(TYPEindex) = name
    FlagSet(TERMS | TYPES | (1L << index))           // error
  }

  final val JavaStatic = commonFlag(31, "<static>")  // error
  final val JavaStaticTerm = JavaStatic.toTermFlags  // error
}
