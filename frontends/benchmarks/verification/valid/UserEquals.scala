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
}
