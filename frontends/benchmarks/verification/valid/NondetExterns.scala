import stainless.lang._
import stainless.annotation._

object NondetExterns {
  // A clock: each call may return a different time
  @extern @nondet
  def now(): BigInt = {
    (??? : BigInt)
  }.ensuring(res => res >= 0)

  // A solver call: the same query may get different answers
  @extern @nondet
  def check(query: BigInt): Option[Boolean] = {
    (??? : Option[Boolean])
  }.ensuring(res => query != 0 || res != Some(false))

  // Deterministic externs still return equal results for equal arguments
  @extern
  def hash(x: BigInt): BigInt = {
    (??? : BigInt)
  }.ensuring(res => res >= 0)

  def hashTwice(x: BigInt): Unit = {
    val a = hash(x)
    val b = hash(x)
    assert(a == b)
  }

  def elapsed(): BigInt = {
    val start = now()
    val end = now()
    end - start + start
  }.ensuring(res => res >= 0)

  def checkZero(): Boolean = {
    check(0) match {
      case Some(b) => b
      case None() => true
    }
  }.ensuring(res => res)

  // Callers of nondeterministic functions are nondeterministic too
  def retry(n: BigInt): Option[Boolean] = {
    require(n >= 0)
    decreases(n)
    val r = check(0)
    if (r.isDefined || n == 0) r else retry(n - 1)
  }.ensuring(res => res != Some(false))

  class Clock {
    @extern @nondet
    def tick(): BigInt = {
      (??? : BigInt)
    }.ensuring(res => res > 0)
  }

  def ticks(c: Clock): BigInt = {
    val a = c.tick()
    val b = c.tick()
    a + b
  }.ensuring(res => res > 1)
}
