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
  case object Empty extends Tree
  case class Tip() extends Tree

  abstract class Base
  case class Named(name: String) extends Base {
    override def toString: String = name
  }

  // On the JVM, its string shows its address: Stainless leaves it uninterpreted
  class Counter(val n: BigInt)

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

  // Case classes and case objects get the `toString` that the compiler synthesizes
  def caseClasses(p: Point, id: Id, l: Tree, r: Tree): Unit = {
    assert(s"$p" == "Point(" + p.x.toString + "," + p.y.toString + ")")
    assert(s"${Leaf(id)}" == "Leaf(" + id.name + ")")
    assert(Node(l, r).toString == "Node(" + l.toString + "," + r.toString + ")")
    assert(Empty.toString == "Empty")
    assert(Tip().toString == "Tip()")
  }

  // Calls through a parent class dispatch to the `toString` of the subclass
  def dispatch(t: Tree, id: Id): Unit = {
    assert(t.toString.bigLength() >= 0)
    assert(t != Empty ==> (t.toString.bigLength() > 4))
    val leaf: Tree = Leaf(id)
    assert(leaf.toString == "Leaf(" + id.name + ")")
    val named: Named = Named("x")
    assert(named.toString == "x")
  }

  // Booleans are precise, other values are uninterpreted but deterministic
  def values(b: Boolean, x: BigInt, y: Int, c: Counter): Unit = {
    assert(s"$b" == (if (b) "true" else "false"))
    assert(s"x = $x" == "x = " + x.toString)
    assert(s"$y, $c" == y.toString + ", " + c.toString)
    assert(c == new Counter(x) ==> (s"$c" == s"${new Counter(x)}"))
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
