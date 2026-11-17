import stainless.lang._

// A proposition can be decided in Scala, but Stainless doesn't let the value of a term depend on it.
object DecidedDeclaredProposition {
  def positive(f: BigInt => BigInt): Prop = forall((x: BigInt) => f(x) > 0)

  def decide(f: BigInt => BigInt): BigInt = if (positive(f).decide) 1 else 0
}
