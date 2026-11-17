import stainless.lang._

// A refined proposition is still a proposition: the value of a term can't depend on it.
object DecidedByRefinedProposition {
  def isPositive(f: BigInt => BigInt): {r: Prop with !r.decide || f(0) > 0} =
    forall((x: BigInt) => f(x) > 0)

  def decide(f: BigInt => BigInt): BigInt = if (isPositive(f).decide) f(0) else BigInt(1)
}
