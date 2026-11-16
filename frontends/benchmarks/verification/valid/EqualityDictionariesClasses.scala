import stainless.lang._
import stainless.collection._
object EqualityDictionariesClasses {
  case class Id(name: BigInt, tag: BigInt) {
    override def equals(that: Any): Boolean = that match {
      case Id(n, _) => n == name
      case _ => false
    }
  }
  def found: Unit = {
    val l = List(Id(1, 0), Id(2, 0))
    assert(l.contains(Id(2, 5)))
  }
  def ints(l: List[BigInt], x: BigInt): Unit = {
    require(l.content.contains(x))
    assert(l.contains(x))
  }.ensuring(_ => l.contains(x))
}
object EqualityDictionariesClassesGeneric {
  import EqualityDictionariesClasses._
  def weak(l: List[Id], x: Id): Unit = {
    require(l.content.contains(x))
  }.ensuring(_ => l.contains(x))
  def generic[T](l: List[T], x: T): Unit = {
    require(l.content.contains(x))
  }.ensuring(_ => l.contains(x))
  def use = generic(List(Id(1, 1)), Id(1, 1))
  def genericF[T](l: List[T], x: T): Unit = {
    require(formalEquality[T] && l.contains(x))
  }.ensuring(_ => l.content.contains(x))
  def use2 = genericF(List(BigInt(1)), BigInt(1))
}
object EqualityDictionariesClassesUser {
  case class Key(name: BigInt, tag: BigInt) {
    override def equals(that: Any): Boolean = that match {
      case Key(n, _) => n == name
      case _ => false
    }
  }
  sealed abstract class MyList[T] {
    def content: Set[T] = this match {
      case MyNil() => Set.empty[T]
      case MyCons(h, t) => t.content + h
    }
    def contains(v: T): Boolean = (this match {
      case MyCons(h, t) => h == v || t.contains(v)
      case MyNil() => false
    }).ensuring { res =>
      (content.contains(v) ==> res) &&
      (formalEquality[T] ==> (res == content.contains(v)))
    }
  }
  case class MyCons[T](h: T, t: MyList[T]) extends MyList[T]
  case class MyNil[T]() extends MyList[T]
  def use(l: MyList[Key], x: Key) = l.contains(x)
  def ints(l: MyList[BigInt], x: BigInt) = {
    l.contains(x)
  }.ensuring(_ == l.content.contains(x))
}
