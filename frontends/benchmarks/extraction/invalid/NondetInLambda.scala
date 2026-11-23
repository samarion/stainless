import stainless.lang._
import stainless.annotation._

object NondetInLambda {
  @extern @nondet
  def now(): BigInt = (??? : BigInt)

  def times(n: BigInt): BigInt => BigInt = (x: BigInt) => x + now()
}
