class List {
  val sentinel: Node = new Node(null, null, this, null)

  def insert(data: AnyRef) = sentinel.insertAfter(data)
}

import scala.annotation.partial

class Node(var prev: Node, var next: Node, parent: List @partial, data: AnyRef) {
  parent.insert("hello")  // error

  def insertAfter(data: AnyRef) = {
    val node = new Node(this, this.next, this.parent, data)
    next.prev = node
    next = node
  }
}