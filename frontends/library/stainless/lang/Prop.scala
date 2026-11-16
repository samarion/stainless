package stainless.lang

import stainless.annotation._
import scala.language.implicitConversions

/** A proposition: a statement with a truth value that can be stated, assumed and proven, but
  * not decided. Quantifiers are propositions, and so is any function, field or value that is
  * given one.
  *
  * Booleans are propositions, and Scala sees propositions as booleans so that they can be used
  * with `&&`, `require`, `assert` or `ensuring`. Stainless rejects any term whose value would
  * depend on the truth of a proposition, such as `if (forall(...)) 1 else 0`.
  */
@ignore
final class Prop private (private val truth: Boolean)

@ignore
object Prop {
  implicit def fromBoolean(b: Boolean): Prop = new Prop(b)
  implicit def toBoolean(p: Prop): Boolean = p.truth

  // a boolean is a proposition, so the two can be compared
  given CanEqual[Boolean, Prop] = CanEqual.derived
  given CanEqual[Prop, Boolean] = CanEqual.derived
}
