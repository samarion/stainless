package stainless.lang

import stainless.annotation._

/** The specifications that are only checked statically. They take propositions, such as
  * quantifiers, and booleans, which are propositions. */
object StaticChecks {

  @library
  def require(@ghost pred: => Prop): Unit = ()

  @library
  def require(@ghost pred: => Prop, msg: => String): Unit = ()

  @library
  def assert(@ghost pred: => Prop): Unit = ()

  @library
  def assert(@ghost pred: => Prop, msg: => String): Unit = ()

  @library
  implicit class Ensuring[A](val x: A) extends AnyVal {
    def ensuring(@ghost cond: A => Boolean | Prop): A = x

    def ensuring(@ghost cond: A => Boolean | Prop, msg: => String): A = x

    def ensuring(@ghost cond: Prop): A = x

    def ensuring(@ghost cond: Prop, msg: => String): A = x
  }

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

