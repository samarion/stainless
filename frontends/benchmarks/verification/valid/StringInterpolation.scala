import stainless.lang._
import stainless.annotation._
import stainless.collection._

object StringInterpolation {
  case class Id(name: String, n: BigInt) {
    override def toString: String = name
  }

  case class Point(x: BigInt, y: BigInt)

  sealed abstract class Tree
  case class Leaf(id: Id) extends Tree
  case class Node(l: Tree, r: Tree) extends Tree

  // The literal parts, with their escapes, and strings in between
  def literal(s: String): Unit = {
    assert(s"abc" == "abc")
    assert(s"" == "")
    assert(s"a\tb" == "a" + "\t" + "b")
    assert(raw"a\tb" == "a\\tb")
    assert(s"<$s>" == "<" + s + ">")
    assert(s"$s$s" == s + s)
    assert(s"$s".bigLength() == s.bigLength())
  }

  // A `toString` that the user defines
  def overridden(id: Id): Unit = {
    assert(s"Unknown $id" == "Unknown " + id.name)
    assert(id.toString == id.name)
    assert(s"${id.n}" == id.n.toString)
  }

  // Booleans are precise, other values are uninterpreted but deterministic
  def values(b: Boolean, x: BigInt, y: Int, p: Point, t: Tree): Unit = {
    assert(s"$b" == (if (b) "true" else "false"))
    assert(s"x = $x" == "x = " + x.toString)
    assert(s"$y, $p" == y.toString + ", " + p.toString)
    assert(s"$t".bigLength() >= 0)
    assert(p == Point(x, x) ==> (s"$p" == s"${Point(x, x)}"))
  }

  def generic[T](t: T, u: T): Unit = {
    require(t == u)
    assert(s"[$t]" == s"[$u]")
  }

  // `+` on a string and another value
  def concat(x: BigInt, id: Id): Unit = {
    assert("x = " + x == s"x = $x")
    assert("id: " + id == "id: " + id.name)
  }

  case class Exc(msg: String) extends Exception

  def find(ids: List[Id], name: String): Id = {
    ids.find(_.name == name) match {
      case Some(id) => id
      case None() => throw Exc(s"Unknown $name in ${ids.size} ids")
    }
  }.throwing { case Exc(msg) => msg.bigLength() > 0 }
}
