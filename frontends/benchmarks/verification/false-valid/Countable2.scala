import stainless.lang._
import stainless.annotation._

// See https://github.com/epfl-lara/stainless/issues/1180
object Countable2 {
  // an instance of Countable gives a bijection between BigInt => BigInt and BigInt
  // (two functions are the same when they agree on all inputs)
  abstract class Countable {
    @law
    def isBijective = {
      forall((t: BigInt => BigInt, x: BigInt) => g(f(t))(x) == t(x)) &&
      forall((h: BigInt) => f(g(h)) == h)
    }

    def f(x: BigInt => BigInt): BigInt
    def g(x: BigInt): BigInt => BigInt
  }

  type Empty = Countable

  // there is no element of Countable
  // (since there is no bijection between BigInt and BigInt => BigInt)
  def lemma(e: Empty) = {
    assert(e.isBijective)
    val f: (BigInt => BigInt) => BigInt = e.f
    val g: BigInt => (BigInt => BigInt) = e.g
    def d(x: BigInt): BigInt = g(x)(x) + 1
    assert(d(f(d)) == g(f(d))(f(d)) + 1)
    assert(d(f(d)) == d(f(d)) + 1)
    false
  }.holds

  def theorem() = {
    if (forall((x: Empty) => false))
      assert(false) // Inox assumes every type is not empty
    else {
      val e: Empty = choose((x: Empty) => true)
      assert(lemma(e))
      assert(false)
    }
  }
}
