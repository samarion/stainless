import stainless.annotation._

object NondetNotExtern {
  @nondet
  def f(x: BigInt): BigInt = x + 1
}
