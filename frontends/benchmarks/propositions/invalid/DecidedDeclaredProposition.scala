import stainless.lang._

// A proposition is not a boolean: the value of a term can't depend on it.
object DecidedDeclaredProposition {
  def positive(f: BigInt => BigInt): Prop = forall((x: BigInt) => f(x) > 0)

  def decide(f: BigInt => BigInt): BigInt = if (positive(f)) 1 else 0
}
