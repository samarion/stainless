import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.annotation._

// ChooseEmpty as a proof by cases on the quantifier, which Stainless accepts: it proves false
// because Inox assumes that every type has a value, not because of the case split.
object ChooseEmptyCases {

  trait Absurdity {
    @law
    def yes: Boolean = 1 == 2
  }

  def lemma(a: Absurdity) = {
    assert(a.yes)
    false
  }.holds

  def theorem() = {
    forall((x: Absurdity) => false).cases({
      assert(false) // Inox assumes every type is not empty
      ()
    }, {
      val e: Absurdity = choose((x: Absurdity) => true)
      assert(lemma(e))
      assert(false)
      ()
    })
  }
}
