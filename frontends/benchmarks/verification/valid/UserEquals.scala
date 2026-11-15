import stainless.lang._

/** `==` on a class that defines `equals` is a call to that method. */
object UserEquals {
  case class Identifier(name: String, globalId: BigInt) {
    override def equals(that: Any): Boolean = that match {
      case id: Identifier => globalId == id.globalId
      case _ => false
    }
    override def hashCode: Int = 0
  }

  def sameGlobalId: Unit = {
    val x = Identifier("x", 1)
    val y = Identifier("y", 1)
    assert(x == y)
    assert(x.name != y.name)
  }

  def distinct(x: Identifier, y: Identifier): Unit = {
    require(x.globalId != y.globalId)
  }.ensuring(_ => x != y)

  def reflexive(x: Identifier): Unit = {
    ()
  }.ensuring(_ => x == x)

  // An open hierarchy whose root defines `equals`. Its postcondition binds the overrides.
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
