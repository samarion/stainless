import stainless.lang._

object StringInterpolation {
  case class Point(x: BigInt, y: BigInt)
  class Counter(val n: BigInt)

  // The string of a number is uninterpreted: equal strings don't mean equal values
  def injective(p: Point, q: Point): Unit = {
    require(s"$p" == s"$q")
    assert(p == q)
  }

  // So is the one of a class that doesn't override `toString`
  def counter(c: Counter, d: Counter): Unit = {
    require(s"$c" == s"$d")
    assert(c == d)
  }

  def notEmpty(x: BigInt): Unit = {
    assert(s"$x".bigLength() > 0)
  }

  def escapes(): Unit = {
    assert(s"a\tb" == raw"a\tb")
  }
}
