import stainless.lang._
import stainless.lang.StaticChecks._

object ForallWithBlock {
  def g(w: BigInt) = true

  def f() = {
    assert(forall((w: BigInt) => { g(w); true }))
  }
}
