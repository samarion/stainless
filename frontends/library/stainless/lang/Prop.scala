package stainless.lang

import stainless.annotation._
import scala.language.implicitConversions

/** A proposition: a statement with a truth value that can be stated, assumed and proven, but
  * not decided. Quantifiers are propositions, and so is any function, field or value that is
  * declared or given one.
  *
  * Booleans are propositions, but a proposition is not a boolean: it can be combined with
  * `&&`, `||`, `!` and `==>`, and stated with `require`, `assert`, `ensuring` or `holds`, but
  * not decided: `cases` branches on it, between two proofs or two propositions.
  */
@ignore
final class Prop private (private val truth: Boolean) {
  def &&(that: => Prop): Prop = new Prop(truth && that.truth)
  def ||(that: => Prop): Prop = new Prop(truth || that.truth)
  def unary_! : Prop = new Prop(!truth)

  /** A proof by cases: `ifHolds` proves the goal when the proposition holds, and `otherwise`
    * when it doesn't. No value can depend on a proposition, so both cases are proofs. */
  def cases(ifHolds: => Unit, otherwise: => Unit): Unit = if (truth) ifHolds else otherwise

  /** The proposition `ifHolds` when this one holds, and `otherwise` when it doesn't. */
  def cases(ifHolds: => Prop, otherwise: => Prop): Prop = if (truth) ifHolds else otherwise
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
