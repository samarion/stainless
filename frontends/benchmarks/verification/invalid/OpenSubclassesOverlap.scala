import stainless.lang._

object OpenSubclassesOverlap {
  // Classes unknown to the program may extend several open traits
  trait C { def c: BigInt }
  trait D { def d: BigInt }
  case class A() extends C with D {
    def c: BigInt = 1
    def d: BigInt = 2
  }

  def both(x: Any): Unit = {
    require(x.isInstanceOf[C] && x.isInstanceOf[D])
    assert(x.isInstanceOf[A]) // invalid: `class E extends C with D`
  }

  // Open roots of two hierarchies, in sorts of their own
  sealed abstract class Shape
  abstract class Open1 extends Shape { def size: BigInt }
  case class Square() extends Shape
  sealed abstract class Animal
  abstract class Open2 extends Animal { def legs: BigInt }
  case class Dog() extends Animal

  def crossed(s: Shape): Unit = {
    assert(!s.asInstanceOf[Any].isInstanceOf[Animal]) // invalid: `class F extends Open1 with Open2`
  }
}
