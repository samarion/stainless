package stainless.lang

import stainless.annotation._

/** The specifications that are only checked statically: `require`, `assert` and `ensuring`
  * are now those of [[stainless.lang]], which take propositions and are only checked
  * statically too. */
object StaticChecks {

  @library @ignore
  implicit class WhileDecorations(val u: Unit) {
    def invariant(@ghost x: => Boolean): Unit = {
      require(x)
      u
    }

    def noReturnInvariant(@ghost x: => Boolean): Unit = {
      require(x)
      u
    }

    def inline: Unit = { }
    def opaque: Unit = { }
  }

}

