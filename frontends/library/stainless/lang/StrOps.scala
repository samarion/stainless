/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._

/**
 * @author Mikael
 */
object StrOps {
  @ignore
  def concat(a: String, b: String): String = {
    a + b
  }

  @ignore
  def bigLength(s: String): BigInt = {
    BigInt(s.length)
  }

  @ignore
  def bigSubstring(s: String, start: BigInt, end: BigInt): String = {
    s.substring(start.toInt, end.toInt)
  }

  /**
   * The string of `x`, as `x.toString`, which Stainless extracts to it when `x` has no
   * `toString` that Stainless extracts (as for numbers, type parameters or case classes).
   * Stainless keeps it uninterpreted: it only depends on the value of `x`.
   */
  @library @extern @pure
  def valueToString[@mutable T](x: T): String = x.toString
}
