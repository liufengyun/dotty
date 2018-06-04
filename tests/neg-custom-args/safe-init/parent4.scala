object Trees {
  class ValDef {
    def setMods(x: Int) = ???
  }

  class EmptyValDef extends ValDef {
    setMods(5)                                // error
  }

  val theEmptyValDef = new EmptyValDef
}