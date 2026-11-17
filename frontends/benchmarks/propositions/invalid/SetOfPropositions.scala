import stainless.lang._

// A set computes with the equality of its elements, so it can't hold data that holds a
// proposition.
object SetOfPropositions {
  case class Claim(holds: Prop, at: BigInt)

  def props(f: BigInt => BigInt): Set[Claim] = Set(Claim(forall((x: BigInt) => f(x) > 0), 0))
}
