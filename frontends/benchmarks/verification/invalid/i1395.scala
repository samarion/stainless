import stainless.lang._
import stainless.collection._

// Call-by-name arguments are lambdas `() => arg`, and the lambda the recursive
// calls pass is `() => arg()`. `head` fails on `Pair(Node(0, Leaf()), Node(0, Leaf()))`
// whatever `arg` is, but Inox ordered these lambdas inconsistently with their
// equality, and the VC was proved (epfl-lara/inox#389)
object i1395 {
  sealed trait Tree
  case class Leaf() extends Tree
  case class Node(value: BigInt, sub: Tree) extends Tree
  case class Pair(left: Node, right: Node) extends Tree

  def foo(t: Tree, arg: => BigInt): List[BigInt] = {
    decreases(t)
    t match {
      case Leaf() => Nil[BigInt]()
      case Node(_, sub) => foo(sub, arg)
      case Pair(l, r) => Cons(((foo(l, arg) ++ (foo(r, arg) :+ BigInt(1))) - BigInt(1)).head, Nil[BigInt]())
    }
  }
}
