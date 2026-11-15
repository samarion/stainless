import stainless.lang._

// `==` on a type parameter calls the `equals` of the type it is instantiated with.
object EqualityDictionaries {

  case class Identifier(name: String, globalId: BigInt) {
    override def equals(that: Any): Boolean = that match {
      case id: Identifier => globalId == id.globalId
      case _ => false
    }
  }

  sealed abstract class MyList[A]
  case class MyCons[A](head: A, tail: MyList[A]) extends MyList[A]
  case class MyNil[A]() extends MyList[A]

  case class Box[A](value: A, tag: BigInt)

  def contains[A](xs: MyList[A], x: A): Boolean = xs match {
    case MyNil() => false
    case MyCons(h, t) => h == x || contains(t, x)
  }

  // The dictionary is passed along
  def containsBoth[A](xs: MyList[A], x: A, y: A): Boolean = contains(xs, x) && contains(xs, y)

  def same[A](x: Box[A], y: Box[A]): Boolean = x == y

  def samePair[A, B](x: (A, B), y: (A, B)): Boolean = x == y

  // Not compared, so no dictionary
  def length[A](xs: MyList[A]): BigInt = {
    xs match {
      case MyNil() => BigInt(0)
      case MyCons(_, t) => 1 + length(t)
    }
  }.ensuring(_ >= 0)

  // Equality in the logic implies `==`, for any type
  def containsHead[A](xs: MyCons[A]): Boolean = {
    contains(xs, xs.head)
  }.holds

  def test: Unit = {
    val x = Identifier("x", 1)
    val y = Identifier("y", 1)
    val z = Identifier("x", 2)

    assert(contains(MyCons(x, MyNil[Identifier]()), y))
    assert(!contains(MyCons(x, MyNil[Identifier]()), z))
    assert(containsBoth(MyCons(x, MyNil[Identifier]()), x, y))

    assert(same(Box(x, 0), Box(y, 0)))
    assert(!same(Box(x, 0), Box(y, 1)))
    assert(samePair((x, BigInt(1)), (y, BigInt(1))))

    // Compared structurally, with `equals` on the identifiers
    assert(MyCons(x, MyNil[Identifier]()) == MyCons(y, MyNil[Identifier]()))
    assert(MyCons(x, MyNil[Identifier]()) != MyCons(z, MyNil[Identifier]()))
    assert((x, BigInt(1)) == (y, BigInt(1)))

    // The equality of the logic, where no class defines `equals`
    assert(contains(MyCons(BigInt(1), MyNil[BigInt]()), BigInt(1)))
    assert(!contains(MyCons(BigInt(1), MyNil[BigInt]()), BigInt(2)))
  }
}
