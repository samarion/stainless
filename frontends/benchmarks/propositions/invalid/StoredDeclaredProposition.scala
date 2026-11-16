import stainless.lang._

// A proposition can't be an element of a set, even when it is declared.
object StoredDeclaredProposition {
  def positive(f: BigInt => BigInt): Prop = forall((x: BigInt) => f(x) > 0)

  def props(f: BigInt => BigInt): Set[Prop] = Set(positive(f))
}
