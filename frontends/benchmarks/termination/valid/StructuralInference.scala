import stainless.lang._
import stainless.collection._

// Measures inferred from the subterm order: a parameter, a lexicographic tuple of parameters, and
// parameters of mutually recursive functions. `Expr` has two parents, so its classes are constructors
// of the Object sort.
object StructuralInference {
  trait Typed
  sealed abstract class Expr extends Typed
  case class Lit(v: BigInt) extends Expr
  case class Neg(e: Expr) extends Expr
  case class Plus(l: Expr, r: Expr) extends Expr

  def eval(e: Expr): BigInt = e match {
    case Lit(v) => v
    case Neg(inner) => -eval(inner)
    case Plus(l, r) => eval(l) + eval(r)
  }

  def evalPos(e: Expr): BigInt = e match {
    case Lit(v) => v
    case Neg(inner) => evalNeg(inner)
    case Plus(l, r) => evalPos(l) + evalPos(r)
  }

  def evalNeg(e: Expr): BigInt = e match {
    case Lit(v) => -v
    case Neg(inner) => evalPos(inner)
    case Plus(l, r) => evalNeg(l) + evalNeg(r)
  }

  sealed abstract class Nat
  case class Succ(n: Nat) extends Nat
  case class Zero() extends Nat

  def ackermann(m: Nat, n: Nat): Nat = (m, n) match {
    case (Zero(), _) => Succ(n)
    case (Succ(m1), Zero()) => ackermann(m1, Succ(Zero()))
    case (Succ(m1), Succ(n1)) => ackermann(m1, ackermann(m, n1))
  }

  def subseq[T](l1: List[T], l2: List[T]): Boolean = (l1, l2) match {
    case (Nil(), _) => true
    case (Cons(x, xs), Cons(y, ys)) => (x == y && subseq(xs, ys)) || subseq(l1, ys)
    case _ => false
  }
}
