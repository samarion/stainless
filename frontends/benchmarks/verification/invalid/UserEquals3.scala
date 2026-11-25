import stainless.lang._

object UserEquals3 {
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

  // An override that breaks the postcondition of the `equals` it overrides
  case class Leaf(key: BigInt, label: String) extends Tree {
    override def equals(that: Any): Boolean = that match {
      case l: Leaf => key == l.key && label == l.label
      case _ => false
    }
  }
}
