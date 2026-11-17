import stainless.lang._
import stainless.lang.StaticChecks._

// Quantifiers that only state specifications: predicate definitions, lemmas that hold,
// named propositions, preconditions and assertions.
object Lemmas {
  def isAssociative(f: (BigInt, BigInt) => BigInt): Prop =
    forall((x: BigInt, y: BigInt, z: BigInt) => f(f(x, y), z) == f(x, f(y, z)))

  def isCommutative(f: (BigInt, BigInt) => BigInt): Prop =
    forall((x: BigInt, y: BigInt) => f(x, y) == f(y, x))

  // a predicate defined from other predicates
  def isMonoidal(f: (BigInt, BigInt) => BigInt): Prop =
    isAssociative(f) && isCommutative(f)

  // the result of the postcondition is a proposition
  def additionIsMonoidal: Prop = {
    isMonoidal((x: BigInt, y: BigInt) => x + y)
  }.holds

  // a proposition can be named, and choose between propositions
  def swapped(f: (BigInt, BigInt) => BigInt, a: BigInt, b: BigInt): Prop = {
    require(isCommutative(f))
    val commutes = isCommutative(f)
    assert(commutes)
    commutes.cases(f(a, b) == f(b, a), isAssociative(f))
  }.holds

  // a term that doesn't depend on the propositions that are stated around it
  def apply(f: (BigInt, BigInt) => BigInt, a: BigInt, b: BigInt): BigInt = {
    require(isCommutative(f))
    f(a, b)
  }.ensuring(res => res == f(b, a) && isCommutative(f))
}
