import stainless.lang._

object StructuralMeasureGeneric {
  case class Box[T](v: T)

  sealed abstract class E
  case class W(b: Box[E]) extends E
  case class Z() extends E

  // The size of a `Box[T]` doesn't count its `T` field, so the measure doesn't decrease
  def throughBox(e: E): BigInt = {
    decreases(e)
    e match {
      case W(b) => throughBox(b.v)
      case Z() => BigInt(0)
    }
  }

  sealed abstract class L
  case class C(h: BigInt, t: L) extends L
  case class N() extends L

  def rebuild(l: L): BigInt = {
    decreases(l)
    l match {
      case C(_, t) => rebuild(C(1, t))
      case N() => BigInt(0)
    }
  }
}
