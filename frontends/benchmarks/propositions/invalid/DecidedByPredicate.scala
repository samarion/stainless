import stainless.lang._

// A function that is given a predicate that states a quantifier can't branch on it.
object DecidedByPredicate {
  def count(p: BigInt => Prop): BigInt = if (p(0).decide) BigInt(1) else BigInt(0)

  def test(f: BigInt => BigInt): BigInt = count((y: BigInt) => forall((x: BigInt) => f(x) < y))
}
