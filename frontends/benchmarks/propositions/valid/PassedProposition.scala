import stainless.lang._

// A proposition is a value: it can be passed to a function that only states it.
object PassedProposition {
  def negate(b: Prop): Prop = !b
  def test(f: BigInt => BigInt): Prop = negate(forall((x: BigInt) => f(x) > 0))
}
