import stainless.lang._

object UserEquals2 {
  // An `equals` that is not reflexive
  case class Odd(value: BigInt) {
    override def equals(that: Any): Boolean = that match {
      case o: Odd => value < o.value
      case _ => false
    }
    override def hashCode: Int = 0
  }
}
