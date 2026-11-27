import stainless.lang._

object StructuralMeasureGeneric {
  case class Box[T](v: T)

  sealed abstract class E
  case class W(b: Box[E]) extends E
  case class Z() extends E

  // `b.v` is a subterm of `e`, but through a field whose type is a type parameter of `Box`, which the size
  // of `E` doesn't count. Such subterms aren't accepted, as the measures that aren't subterms of one
  // another are compared by their size.
  def throughBox(e: E): BigInt = {
    decreases(e)
    e match {
      case W(b) => throughBox(b.v)
      case Z() => BigInt(0)
    }
  }
}
