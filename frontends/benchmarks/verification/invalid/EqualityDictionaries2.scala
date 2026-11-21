import stainless.lang._

object EqualityDictionaries2 {

  case class Identifier(name: String, globalId: BigInt) {
    override def equals(that: Any): Boolean = that match {
      case id: Identifier => globalId == id.globalId
      case _ => false
    }
  }

  def same[A](x: A, y: A): Boolean = x == y

  // `==` doesn't imply equality in the logic
  def congruence[A](x: A, y: A, f: A => BigInt): Boolean = {
    require(same(x, y))
    f(x) == f(y)
  }.holds

  // Without this call, `A` would only be compared as in the logic
  def test: Boolean = congruence(Identifier("x", 1), Identifier("y", 1), (id: Identifier) => BigInt(0))
}
