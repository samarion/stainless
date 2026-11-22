import stainless.lang._
import stainless.collection._

// Recursion over data types that recurse through another data type.
// The size of a list of trees must account for the sizes of the trees.
object NestedDataTypes {

  case class Tree[A](value: A, children: List[Tree[A]])

  // Inferred measures

  def size[A](t: Tree[A]): BigInt = {
    BigInt(1) + sizes(t.children)
  }.ensuring(_ > 0)

  def sizes[A](ts: List[Tree[A]]): BigInt = {
    ts match {
      case Nil() => BigInt(0)
      case Cons(t, rest) => size(t) + sizes(rest)
    }
  }.ensuring(_ >= 0)

  // Given measures

  def mirror[A](t: Tree[A]): Tree[A] = {
    decreases(t)
    Tree(t.value, mirrors(t.children))
  }

  def mirrors[A](ts: List[Tree[A]]): List[Tree[A]] = {
    decreases(ts)
    ts match {
      case Nil() => Nil[Tree[A]]()
      case Cons(t, rest) => mirrors(rest) :+ mirror(t)
    }
  }

  // Through two data types

  sealed abstract class Expr
  case class Lit(value: BigInt) extends Expr
  case class Call(name: BigInt, args: Option[List[Expr]]) extends Expr

  def depth(e: Expr): BigInt = {
    e match {
      case Lit(_) => BigInt(0)
      case Call(_, None()) => BigInt(1)
      case Call(_, Some(args)) => BigInt(1) + depths(args)
    }
  }.ensuring(_ >= 0)

  def depths(es: List[Expr]): BigInt = {
    es match {
      case Nil() => BigInt(0)
      case Cons(e, rest) =>
        val (d, ds) = (depth(e), depths(rest))
        if (d >= ds) d else ds
    }
  }.ensuring(_ >= 0)

  // Through a tuple

  case class Rec(fields: List[(BigInt, Rec)])

  def count(r: Rec): BigInt = {
    BigInt(1) + counts(r.fields)
  }.ensuring(_ > 0)

  def counts(fs: List[(BigInt, Rec)]): BigInt = {
    fs match {
      case Nil() => BigInt(0)
      case Cons((_, r), rest) => count(r) + counts(rest)
    }
  }.ensuring(_ >= 0)
}
