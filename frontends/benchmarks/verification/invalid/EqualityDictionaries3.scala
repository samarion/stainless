import stainless.lang._
import stainless.collection._
object EqualityDictionaries3 {
  case class Id(name: BigInt, tag: BigInt) {
    override def equals(that: Any): Boolean = that match {
      case Id(n, _) => n == name
      case _ => false
    }
  }
  def wrong(l: List[Id], x: Id): Unit = {
    require(l.contains(x))
    assert(l.content.contains(x))
  }
}
