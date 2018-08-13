object Flags {
  private final val TERMindex = 0
  private final val TYPEindex = 1
  private final val TERMS = 1 << TERMindex
  private final val TYPES = 1 << TYPEindex
  private final val KINDFLAGS = TERMS | TYPES

  case class FlagSet(val bits: Long) {
    def toTermFlags =
      if (bits == 0) this
      else FlagSet(bits & ~KINDFLAGS | TERMS)
  }
  final val JavaStatic = FlagSet(31)
  final val JavaStaticTerm = JavaStatic.toTermFlags
}