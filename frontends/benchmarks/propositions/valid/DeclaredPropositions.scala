import stainless.lang._
import stainless.lang.StaticChecks._

// Propositions can be declared: `forall` is a `Prop`, and so can be results, parameters,
// fields and tuple components. Booleans are propositions.
object DeclaredPropositions {
  case class Claim(holds: Prop, at: BigInt)

  def positive(f: BigInt => BigInt): Prop = forall((x: BigInt) => f(x) > 0)

  def both(f: BigInt => BigInt, g: BigInt => BigInt): Prop = positive(f) && positive(g)

  def claim(f: BigInt => BigInt): Claim = Claim(positive(f), 0)

  def pair(f: BigInt => BigInt): (Prop, BigInt) = (positive(f), 1)

  def trivial: Prop = 1 > 0

  def stated(p: Prop): Prop = p

  def use(f: BigInt => BigInt, g: BigInt => BigInt): Unit = {
    require(both(f, g) && claim(f).holds)
    assert(f(3) > 0 && g(4) > 0)
  }.ensuring(_ => positive(g) && pair(f)._1 && stated(trivial))

  def nested(f: BigInt => BigInt): Prop =
    forall((x: BigInt) => forall((y: BigInt) => f(x) + f(y) == f(y) + f(x)))

  def commutes(f: BigInt => BigInt): Unit = ().ensuring(_ => nested(f))

  def weaken(f: BigInt => BigInt): Unit = {
    require(positive(f))
  }.ensuring(_ => forall((x: BigInt) => f(x) >= 0))

  def implied(f: BigInt => BigInt): Prop = positive(f) ==> forall((x: BigInt) => f(x) >= 0)

  def holdsProp(f: BigInt => BigInt): Prop = {
    require(positive(f))
    positive(f)
  }.holds

  def equivalent(f: BigInt => BigInt, b: Boolean): Prop = b == positive(f)
}
