import stainless.lang._

// `Expr` has two parents, so its classes are constructors of the Object sort, and the
// measure `decreases(e)` compares values of Object
object StructuralMeasureObject {
  trait Typed
  sealed abstract class Expr extends Typed
  case class Lit(v: BigInt) extends Expr
  case class Neg(e: Expr) extends Expr
  case class Plus(l: Expr, r: Expr) extends Expr
  case class Pair(p: (Expr, Expr)) extends Expr

  def eval(e: Expr): BigInt = {
    decreases(e)
    e match {
      case Lit(v) => v
      case Neg(Neg(inner)) => eval(inner)
      case Neg(inner) => -eval(inner)
      case Plus(l, r) => eval(l) + eval(r)
      case Pair(p) => eval(p._1) + eval(p._2)
    }
  }

  def leftmost(e: Expr): Expr = {
    decreases(e)
    e match {
      case p: Plus => leftmost(p.l)
      case _ => e
    }
  }

  // The argument isn't a subterm of `e`, so the measure is replaced by its size
  def flatten(e: Expr): BigInt = {
    decreases(e)
    e match {
      case Plus(Plus(a, b), r) => flatten(Plus(a, r)) + flatten(b)
      case Plus(l, r) => flatten(l) + flatten(r)
      case _ => BigInt(0)
    }
  }
}
