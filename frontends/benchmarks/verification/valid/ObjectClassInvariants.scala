import stainless.lang._

// The invariants of classes that are not encoded as ADT sorts
// (covariant classes and classes that extend a generic parent at a specific type).
object ObjectClassInvariants {

  case class Box[+A](a: A, height: BigInt) {
    require(height > 0)
    def positive: Boolean = { height > 0 }.ensuring(res => res)
  }

  def box(h: BigInt): Box[BigInt] = {
    require(h > 3)
    Box(BigInt(1), h)
  }

  def unbox(b: Box[BigInt]): BigInt = {
    b.height
  }.ensuring(_ > 0)

  sealed abstract class S[A]
  case class G[A](height: BigInt) extends S[(A, A)] {
    require(height > 0)
    def positive: Boolean = { height > 0 }.ensuring(res => res)
  }

  def unpack[A](g: G[A]): BigInt = {
    g.height
  }.ensuring(_ > 0)

  sealed abstract class T[A]
  case class H(height: BigInt) extends T[BigInt] {
    require(height > 0)
    def positive: Boolean = { height > 0 }.ensuring(res => res)
  }

  def h(x: BigInt): T[BigInt] = {
    require(x > 0)
    H(x)
  }

  sealed abstract class Nat[+A] {
    def height: BigInt
  }
  case class Leaf[+A](a: A) extends Nat[A] {
    def height: BigInt = 0
  }
  case class Node[+A](left: Nat[A], right: Nat[A], h: BigInt) extends Nat[A] {
    require(0 <= left.height && left.height < h && 0 <= right.height && right.height < h)
    def height: BigInt = h
  }

  def leftIsSmaller[A](n: Node[A]): Boolean = {
    n.left.height < n.height
  }.holds
}
