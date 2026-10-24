import stainless.lang._
import stainless.annotation._

object GhostFunctionEquality {
  case class Box(f: BigInt => BigInt)

  // Functions are equal when they agree on every input
  @ghost
  def sameBoxes(a: BigInt, b: BigInt) = {
    require(a + b == b + a)
    Box(x => x + a + b) == Box(x => x + b + a)
  }.holds

  @ghost
  def compose(f: BigInt => BigInt) = {
    ((x: BigInt) => f(x)) == f
  }.holds
}
