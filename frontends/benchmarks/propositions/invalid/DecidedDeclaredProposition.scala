import stainless.lang._

// Scala sees a proposition as a boolean, but Stainless doesn't let a term decide one.
object DecidedDeclaredProposition {
  def positive(f: BigInt => BigInt): Prop = forall((x: BigInt) => f(x) > 0)

  def decide(f: BigInt => BigInt): BigInt = if (positive(f)) 1 else 0
}
