import stainless.lang._

object UserEquals1 {
  case class Identifier(name: String, globalId: BigInt) {
    override def equals(that: Any): Boolean = that match {
      case id: Identifier => globalId == id.globalId
      case _ => false
    }
    override def hashCode: Int = 0
  }

  // The two identifiers are `==`, although they are not equal in the logic
  def differentNames: Unit = {
    val x = Identifier("x", 1)
    val y = Identifier("y", 1)
    assert(x != y)
  }
}
