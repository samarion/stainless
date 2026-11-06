/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package ast

import org.scalatest.funsuite.AnyFunSuite

/** Unit tests of [[TypeOps.erasePositiveRefinements]] and [[TypeOps.eraseParamRefinements]]. */
class ParamRefinementsSuite extends AnyFunSuite {
  import stainless.trees._

  val symbols = NoSymbols
  import symbols.{erasePositiveRefinements, eraseParamRefinements}

  val zero = IntegerLiteral(BigInt(0))

  def positive(name: String, tpe: Type = IntegerType()): RefinementType = {
    val v = ValDef.fresh(name, tpe)
    RefinementType(v, GreaterThan(v.toVariable, zero))
  }

  test("refinements are erased") {
    assert(erasePositiveRefinements(positive("x")) == IntegerType())
    assert(erasePositiveRefinements(positive("x", positive("y"))) == IntegerType())
    assert(erasePositiveRefinements(TupleType(Seq(positive("x"), BooleanType()))) ==
      TupleType(Seq(IntegerType(), BooleanType())))
  }

  test("function domains are kept") {
    val dom = positive("x")
    assert(erasePositiveRefinements(FunctionType(Seq(dom), positive("y"))) ==
      FunctionType(Seq(dom), IntegerType()))

    val a = ValDef.fresh("a", dom)
    assert(erasePositiveRefinements(PiType(Seq(a), positive("y"))) == PiType(Seq(a), IntegerType()))
  }

  test("sigma binders are erased in the types that refer to them") {
    // (a: { a | a > 0 }, { x | x < a } => BigInt)
    val a = ValDef.fresh("a", positive("a"))
    val x = ValDef.fresh("x", IntegerType())
    val dom = RefinementType(x, LessThan(x.toVariable, a.toVariable))
    val SigmaType(Seq(na), FunctionType(Seq(RefinementType(nx, pred)), IntegerType())) =
      erasePositiveRefinements(SigmaType(Seq(a), FunctionType(Seq(dom), IntegerType()))): @unchecked

    assert(na.id == a.id && na.tpe == IntegerType())
    assert(nx == x)
    assert(pred == LessThan(x.toVariable, na.toVariable))
  }

  test("parameter refinements are erased") {
    // def f(x: { x | x > 0 }, y: { y | y > x }): { r | r > x } = x + y
    val x = ValDef.fresh("x", positive("x"))
    val yv = ValDef.fresh("y", IntegerType())
    val y = ValDef.fresh("y", RefinementType(yv, GreaterThan(yv.toVariable, x.toVariable)))
    val r = ValDef.fresh("r", IntegerType())
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(x, y),
      RefinementType(r, GreaterThan(r.toVariable, x.toVariable)), Plus(x.toVariable, y.toVariable), Seq())

    val nfd = eraseParamRefinements(fd)
    val Seq(nx, ny) = nfd.params: @unchecked
    assert(nx.id == x.id && nx.tpe == IntegerType())
    assert(ny.id == y.id && ny.tpe == IntegerType())
    assert(nfd.returnType == RefinementType(r, GreaterThan(r.toVariable, nx.toVariable)))
    assert(nfd.fullBody == Plus(nx.toVariable, ny.toVariable))
  }

  test("functions without parameter refinements are unchanged") {
    val x = ValDef.fresh("x", FunctionType(Seq(positive("y")), IntegerType()))
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(x), IntegerType(), zero, Seq())
    assert(eraseParamRefinements(fd) eq fd)
  }
}
