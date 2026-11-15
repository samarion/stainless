import stainless.lang._

object ObjectClassInvariants1 {

  case class Box[+A](a: A, height: BigInt) {
    require(height > 0)
  }

  def box(h: BigInt): Box[BigInt] = Box(BigInt(1), h) // The invariant doesn't hold
}
