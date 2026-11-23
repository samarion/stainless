import stainless.lang._

object StringInterpolation {
  case class Point(x: BigInt, y: BigInt)

  // The string of a value is uninterpreted: equal strings don't mean equal values
  def injective(p: Point, q: Point): Unit = {
    require(s"$p" == s"$q")
    assert(p == q)
  }

  def notEmpty(x: BigInt): Unit = {
    assert(s"$x".bigLength() > 0)
  }

  def escapes(): Unit = {
    assert(s"a\tb" == raw"a\tb")
  }
}
