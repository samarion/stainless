/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class UncheckedSuite extends VerificationComponentTestSuite {
  private val solvers = Seq("smt-z3", "smt-cvc4", "smt-cvc5")

  override def configurations: Seq[Seq[inox.OptionValue[?]]] = {
    solvers.flatMap { solver =>
      super.configurations.map {
        seq => Seq(
          inox.optSelectedSolvers(Set(solver)),
          optFailEarly(true),
          inox.solvers.optCheckModels(false)) ++ seq
      }
    }
  }

  // CVC4 doesn't give up on the retract queries of these paradoxes before the timeout
  override def filter(ctx: inox.Context, name: String): FilterStatus = {
    val solvers = ctx.options.findOptionOrDefault(inox.optSelectedSolvers)
    if (solvers == Set("smt-cvc4") && slowOnCVC4(name)) Ignore else super.filter(ctx, name)
  }

  private val slowOnCVC4 = Set(
    "verification/unchecked-invalid/Berardi1",
    "verification/unchecked-invalid/Berardi2",
  )

  import UncheckedSuite._
  testUncheckedAll("verification/unchecked-invalid", uncheckedInvalid)
  testUncheckedAll("verification/unchecked-valid", uncheckedValid)
}
object UncheckedSuite {
  private lazy val uncheckedInvalid = ComponentTestSuite.loadPrograms("verification/unchecked-invalid")
  private lazy val uncheckedValid = ComponentTestSuite.loadPrograms("verification/unchecked-valid")
}
