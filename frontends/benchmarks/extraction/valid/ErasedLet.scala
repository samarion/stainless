import stainless.lang.StaticChecks._

import stainless.lang.{require, assert, Ensuring}
object ErasedLet {
  case class A() {
    def |:(x: Int): Boolean = true
  }

  object A {
    def f(erased x: Int, e: A) = assert(x |: e)
  }
}
