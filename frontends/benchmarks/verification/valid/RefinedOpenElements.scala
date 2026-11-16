import stainless.lang._
import stainless.collection._

object RefinedOpenElements {
  abstract class Tree
  sealed abstract class Expr extends Tree
  case class Lit(v: BigInt) extends Expr
  case class Neg(e: Expr) extends Expr

  type LitExpr = { e: Expr with e.isInstanceOf[Lit] }

  def isPositive(e: Expr, b: BigInt): Boolean = e.isInstanceOf[Lit] && b > 0

  def size(es: List[Expr]): BigInt = (es match {
    case Cons(h, t) => 1 + size(t)
    case Nil() => BigInt(0)
  }).ensuring(_ >= 0)

  def head(es: List[LitExpr]): BigInt = es match {
    case Cons(e, rest) =>
      assert(e.isInstanceOf[Lit])
      0
    case Nil() => 1
  }

  def sum(es: List[LitExpr]): BigInt = es match {
    case Cons(Lit(v), rest) => v + sum(rest)
    case Nil() => 0
  }

  def headWith(b: BigInt, es: List[{ e: Expr with isPositive(e, b) }]): BigInt = es match {
    case Cons(e, rest) =>
      assert(b > 0)
      0
    case Nil() => 1
  }

  def get(o: Option[LitExpr]): BigInt = o match {
    case Some(Lit(v)) => v
    case None() => 0
  }

  def pair(p: (LitExpr, List[LitExpr])): BigInt = p match {
    case (Lit(v), Cons(Lit(w), _)) => v + w
    case (Lit(v), _) => v
  }
}
