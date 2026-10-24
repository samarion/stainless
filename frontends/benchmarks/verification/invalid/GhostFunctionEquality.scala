import stainless.lang._
import stainless.annotation._

object GhostFunctionEquality {
  case class Box(f: BigInt => BigInt)

  @ghost
  def differentBoxes(a: BigInt) = {
    Box(x => x + a) == Box(x => x)
  }.holds
}
