import stainless.lang._

/** `==` on an open hierarchy whose root defines `equals`. */
object UserEqualsOpen {
  // The postcondition of `equals` binds its overrides
  abstract class Tree {
    def key: BigInt
    override def equals(that: Any): Boolean = {
      that match {
        case t: Tree => key == t.key
        case _ => false
      }
    }.ensuring(res => that match {
      case t: Tree => res == (key == t.key)
      case _ => !res
    })
    override def hashCode: Int = 0
  }

  case class Leaf(key: BigInt, label: String) extends Tree

  case class Node(key: BigInt, left: Tree, right: Tree) extends Tree {
    override def equals(that: Any): Boolean = that match {
      case t: Tree => t.key == key
      case _ => false
    }
  }

  def trees(a: Tree, b: Tree): Boolean = {
    require(a.key == b.key)
    a == b
  }.ensuring(res => res)

  def leaves: Unit = {
    assert(Leaf(1, "a") == Leaf(1, "b"))
  }
}
