import stainless.lang._
import stainless.annotation._

object NondetExterns {
  @extern @nondet
  def now(): BigInt = {
    (??? : BigInt)
  }.ensuring(res => res >= 0)

  // Two calls may return different results
  def sameTime(): Unit = {
    val a = now()
    val b = now()
    assert(a == b)
  }

  def twice(): BigInt = now() + now()

  // Also through callers
  def sameTwice(): Unit = {
    val a = twice()
    val b = twice()
    assert(a == b)
  }

  class Clock {
    @extern @nondet
    def tick(): BigInt = {
      (??? : BigInt)
    }.ensuring(res => res > 0)
  }

  def sameTick(c: Clock): Unit = {
    val a = c.tick()
    val b = c.tick()
    assert(a == b)
  }
}
