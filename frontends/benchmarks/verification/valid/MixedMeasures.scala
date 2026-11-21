import stainless.lang._

/** The measure of `g` is propagated to `f`, which has none. The types of the parameters of
  * `g` depend on its type parameter once classes are encoded.
  */
object MixedMeasures {
  case class Box[A](value: A)

  def g[A](b: Box[A], n: BigInt): BigInt = {
    decreases(if (n > 0) n else BigInt(0))
    if (n > 0) f(b, n - 1) else BigInt(0)
  }

  def f[A](b: Box[A], n: BigInt): BigInt = g(b, n)

  def test: BigInt = {
    f(Box(true), 3)
  }.ensuring(_ == 0)
}
