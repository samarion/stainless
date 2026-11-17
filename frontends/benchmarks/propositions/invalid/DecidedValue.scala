import stainless.lang._

// The value of a term can't depend on a quantifier, which has no evaluation rule.
object DecidedValue {
  def isEmpty[A]: BigInt = if (forall((a: A) => false).decide) BigInt(0) else BigInt(1)
}
