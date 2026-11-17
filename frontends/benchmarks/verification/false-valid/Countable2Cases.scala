import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.annotation._

// Countable2 as a proof by cases on the quantifier, which Stainless accepts, with a law that
// doesn't compare functions: it proves false because Inox assumes that every type has a value,
// not because of the case split.
object Countable2Cases {
  // an instance of Countable gives a bijection between BigInt => BigInt and BigInt
  abstract class Countable {
    @law
    def isBijective: Prop = {
      forall((t: BigInt => BigInt, x: BigInt) => g(f(t))(x) == t(x)) &&
      forall((h: BigInt) => f(g(h)) == h)
    }

    def f(x: BigInt => BigInt): BigInt
    def g(x: BigInt): BigInt => BigInt
  }

  // there is no element of Countable
  // (since there is no bijection between BigInt and BigInt => BigInt)
  def lemma(e: Countable) = {
    assert(e.isBijective)
    def d(x: BigInt): BigInt = e.g(x)(x) + 1
    assert(d(e.f(d)) == e.g(e.f(d))(e.f(d)) + 1)
    assert(d(e.f(d)) == d(e.f(d)) + 1)
    false
  }.holds

  def theorem() = {
    forall((x: Countable) => false).cases({
      assert(false) // Inox assumes every type is not empty
      ()
    }, {
      val e: Countable = choose((x: Countable) => true)
      assert(lemma(e))
      assert(false)
      ()
    })
  }
}
