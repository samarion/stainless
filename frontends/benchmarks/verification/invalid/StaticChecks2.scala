import stainless.lang.StaticChecks._

import stainless.lang.{require, assert, Ensuring}
object StaticChecks2 {

  def foo(n: BigInt, m: BigInt) = {
    assert(n + m > n)
  }

}
