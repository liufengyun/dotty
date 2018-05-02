package dotty.runtime

/**
 * Classes used as holders for local lazy vals
 */
class LazyInt {
  var value: Int = 0
  @volatile var initialized: Boolean = false
}

class LazyLong {
  var value: Long = 0
  @volatile var initialized: Boolean = false
}

class LazyBoolean {
  var value: Boolean = false
  @volatile var initialized: Boolean = false
}

class LazyDouble {
  var value: Double = 0
  @volatile var initialized: Boolean = false
}

class LazyByte {
  var value: Byte = 0
  @volatile var initialized: Boolean = false
}

class LazyRef {
  var value: AnyRef = null
  @volatile var initialized: Boolean = false
}

class LazyShort {
  var value: Short = 0
  @volatile var initialized: Boolean = false
}

class LazyChar {
  var value: Char = 0
  @volatile var initialized: Boolean = false
}
