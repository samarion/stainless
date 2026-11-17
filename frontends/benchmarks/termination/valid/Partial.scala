/* From ESOP 2014, Kuwahara et al */

import stainless.lang._
import stainless.lang.StaticChecks._

object Partial {

  def exists[T](p: T => Prop): Prop = {
    !forall((t: T) => !p(t))
  }

  def eliminate_exists[T](p: T => Prop): T = {
    require(exists[T](p))
    choose[T]((res: T) => p(res))
 }.ensuring(p)

  def maxNegP(j: BigInt, p: BigInt => Boolean): Prop = {
    !p(j) && forall((k: BigInt) => !p(k) ==> (k <= j))
  }

  def f(x: BigInt, p: BigInt => Boolean): BigInt = {
    require(!p(x) || exists[BigInt]((j: BigInt) => j < x && maxNegP(j, p)))
    decreases(if (!p(x)) BigInt(0) else x - eliminate_exists[BigInt]((j: BigInt) => j < x && maxNegP(j, p)))
    if (p(x)) {
      f(x - 1, p)
    } else {
      x
    }
  }
}
