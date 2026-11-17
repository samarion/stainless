import stainless.lang.StaticChecks._

import stainless.lang.{require, assert, Ensuring}
object i1408b {
  def test(): Int = {
    5
 }.ensuring(_ == {
    val x = scala.Option(2)
    5
  })
}
