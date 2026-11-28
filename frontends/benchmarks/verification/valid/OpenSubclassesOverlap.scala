import stainless.lang._

object OpenSubclassesOverlap {
  trait C { def c: BigInt; val k: BigInt }
  trait D { def d: BigInt }
  case class A(k: BigInt) extends C with D {
    def c: BigInt = 1
    def d: BigInt = 2
  }

  // An unknown object keeps its fields and its methods across views
  def views(x: C): Unit = {
    require(x.isInstanceOf[D])
    val y = x.asInstanceOf[Any]
    val z = y.asInstanceOf[C]
    assert(z.c == x.c)
    assert(z.k == x.k)
    assert(y.asInstanceOf[D].d == x.asInstanceOf[D].d)
  }

  def known: Unit = {
    val a: Any = A(3)
    assert(a.isInstanceOf[C] && a.isInstanceOf[D])
    assert(a.asInstanceOf[C].k == 3)
  }

  sealed abstract class Shape
  abstract class Open1 extends Shape { def size: BigInt }
  case class Square() extends Shape
  sealed abstract class Animal
  abstract class Open2 extends Animal { def legs: BigInt }
  case class Dog() extends Animal

  def crossed(s: Shape): Unit = {
    require(s.asInstanceOf[Any].isInstanceOf[Animal])
    assert(s.isInstanceOf[Open1])
    val a = s.asInstanceOf[Any].asInstanceOf[Animal]
    assert(a.isInstanceOf[Open2])
    assert(a.asInstanceOf[Any].asInstanceOf[Shape].asInstanceOf[Open1].size == s.asInstanceOf[Open1].size)
  }
}
