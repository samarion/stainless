import stainless.lang._
import stainless.lang.StaticChecks._

object AssociativityProperties {

  def isAssociative[A](f: (A,A) => A): Prop = {
    forall((x: A, y: A, z: A) => f(f(x, y), z) == f(x, f(y, z)))
  }

  def isCommutative[A](f: (A,A) => A): Prop = {
    forall((x: A, y: A) => f(x, y) == f(y, x))
  }

  def isRotate[A](f: (A,A) => A): Prop = {
    forall((x: A, y: A, z: A) => f(f(x, y), z) == f(f(y, z), x))
  }

  def assocNotCommutative[A](f: (A,A) => A): Prop = {
    require(isAssociative(f))
    isCommutative(f)
  }.holds

  def commNotAssociative[A](f: (A,A) => A): Prop = {
    require(isCommutative(f))
    isAssociative(f)
  }.holds
}
