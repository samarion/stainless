import stainless.lang._

// The refinement of a proposition states what holds of it, here in terms of the arguments
// of the predicate. A refined proposition is still a proposition.
object RefinedPredicates {
  def isPositive(f: BigInt => BigInt): {r: Prop with !r.decide || f(0) > 0} =
    forall((x: BigInt) => f(x) > 0)

  def arePositive(f: BigInt => BigInt, g: BigInt => BigInt): Prop =
    isPositive(f) && isPositive(g)

  def named(f: BigInt => BigInt): Prop = {
    val positive: {p: Prop with !p.decide || f(0) > 0} = isPositive(f)
    !positive || f(0) > 0
  }.holds
}
