import stainless.lang._

object EqualityDictionaries1 {

  case class Identifier(name: String, globalId: BigInt) {
    override def equals(that: Any): Boolean = that match {
      case id: Identifier => globalId == id.globalId
      case _ => false
    }
  }

  sealed abstract class MyList[A]
  case class MyCons[A](head: A, tail: MyList[A]) extends MyList[A]
  case class MyNil[A]() extends MyList[A]

  def contains[A](xs: MyList[A], x: A): Boolean = xs match {
    case MyNil() => false
    case MyCons(h, t) => h == x || contains(t, x)
  }

  def test: Unit = {
    val x = Identifier("x", 1)
    val y = Identifier("y", 1)
    assert(!contains(MyCons(x, MyNil[Identifier]()), y)) // The identifiers are equal
  }
}
