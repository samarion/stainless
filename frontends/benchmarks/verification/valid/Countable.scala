import stainless.lang._
import stainless.proof._

object Countable {
  // an instance of Countable gives an injection of BigInt => BigInt into BigInt
  // (two functions are the same when they agree on all inputs)
  trait Countable {
    def f(t: BigInt => BigInt): BigInt
    def g(x: BigInt): BigInt => BigInt

    def gof(t: BigInt => BigInt, x: BigInt) = {
      (??? : Unit)
   }.ensuring(_ => g(f(t))(x) == t(x))
  }

  type Empty = Countable

  // there is no element of Countable
  // since there is no injection of BigInt => BigInt into BigInt
  def lemma(e: Empty) = {
    val f: (BigInt => BigInt) => BigInt = e.f
    val g: BigInt => (BigInt => BigInt) = e.g
    def d(x: BigInt): BigInt = g(x)(x) + 1
    assert(d(f(d)) == g(f(d))(f(d)) + 1)
    e.gof(d, f(d))
    check(d(f(d)) == d(f(d)) + 1)
    false
  }.holds
}
