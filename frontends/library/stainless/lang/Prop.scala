package stainless.lang

import stainless.annotation._
import scala.language.implicitConversions

/** A proposition: a statement with a truth value that can be stated, assumed and proven, but
  * not decided. Quantifiers are propositions, and so is any function, field or value that is
  * declared or given one.
  *
  * Booleans are propositions, but a proposition is not a boolean: it can be combined with
  * `&&`, `||`, `!` and `==>`, and stated with `require`, `assert`, `ensuring` or `holds`, but
  * not used in a condition, except in a proof by cases with `decide`.
  */
@ignore
final class Prop private (private val truth: Boolean) {
  def &&(that: => Prop): Prop = new Prop(truth && that.truth)
  def ||(that: => Prop): Prop = new Prop(truth || that.truth)
  def unary_! : Prop = new Prop(!truth)

  /** Decides the proposition, for a proof by cases: Stainless only accepts a decision on a
    * proposition when no value depends on it, such as a branch between two proofs. */
  def decide: Boolean = truth
}

@ignore
object Prop {
  // `Boolean | Prop` is the result of the predicates given to quantifiers
  implicit def fromBoolean(b: Boolean | Prop): Prop = b match {
    case b: Boolean => new Prop(b)
    case p: Prop => p
  }

  // a boolean is a proposition, so the two can be compared
  given CanEqual[Boolean, Prop] = CanEqual.derived
  given CanEqual[Prop, Boolean] = CanEqual.derived
}
