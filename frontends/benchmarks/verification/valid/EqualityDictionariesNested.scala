import stainless.lang._

// `==` on classes that recurse through another type, whose equality is generated for that type.

object EqualityDictionariesNested {
  case class Identifier(name: String, globalId: BigInt) {
    override def equals(that: Any): Boolean = that match {
      case id: Identifier => globalId == id.globalId
      case _ => false
    }
  }

  sealed abstract class MyList[A]
  case class MyCons[A](head: A, tail: MyList[A]) extends MyList[A]
  case class MyNil[A]() extends MyList[A]

  case class Tree[A](value: A, children: MyList[Tree[A]])

  sealed abstract class Expr
  case class Var(id: Identifier) extends Expr
  case class Call(fun: Identifier, args: MyList[(BigInt, Expr)]) extends Expr

  def same[A](x: A, y: A): Boolean = x == y

  def test: Unit = {
    val x = Identifier("x", 1)
    val y = Identifier("y", 1)
    val z = Identifier("z", 2)
    val tx = Tree(x, MyCons(Tree(x, MyNil[Tree[Identifier]]()), MyNil[Tree[Identifier]]()))
    val ty = Tree(y, MyCons(Tree(y, MyNil[Tree[Identifier]]()), MyNil[Tree[Identifier]]()))
    val tz = Tree(y, MyCons(Tree(z, MyNil[Tree[Identifier]]()), MyNil[Tree[Identifier]]()))
    assert(tx == ty)
    assert(tx != tz)
    assert(same(tx, ty))
    assert(same(MyCons(tx, MyNil[Tree[Identifier]]()), MyCons(ty, MyNil[Tree[Identifier]]())))

    val ex: Expr = Call(x, MyCons((BigInt(0), Var(x)), MyNil[(BigInt, Expr)]()))
    val ey: Expr = Call(y, MyCons((BigInt(0), Var(y)), MyNil[(BigInt, Expr)]()))
    assert(ex == ey)
  }

  def reflexive(e: Expr): Boolean = { e == e }.holds
}
