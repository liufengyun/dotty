class List {
  val sentinel: Node = new Node(this, this, this, null)

  def insert(AnyRef data) = sentinel.insertAfte(data)
}

class Node(val prev: Node, val next: Node, parent: List, data: AnyRef) {
  def insertAfter(data: AnyRef) = {
    val node = new Node(this, this.next, this.parent, data)
    next.prev = node
    next = node
  }
}