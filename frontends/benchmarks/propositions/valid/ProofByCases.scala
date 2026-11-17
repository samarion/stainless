import stainless.lang._
import stainless.annotation._

// A term of type Unit is a proof: a term can decide a quantifier to choose between two of
// them, which is a proof by cases. No value depends on the quantifier.
object ProofByCases {
  def isPositive(f: BigInt => BigInt): Prop = forall((x: BigInt) => f(x) > 0)

  @ghost
  def positiveAtZero(f: BigInt => BigInt): Unit = {
    require(isPositive(f))
    ()
  }.ensuring(_ => f(0) > 0)

  @ghost
  def cases(f: BigInt => BigInt): Unit = {
    if (isPositive(f).decide) positiveAtZero(f)
    else ()
  }.ensuring(_ => !isPositive(f) || f(0) > 0)
}
