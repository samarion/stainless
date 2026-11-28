/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

/** The subterm order on the values of a sort, which is well-founded. Measures of ADT type are compared by
 *  this order where it applies, which avoids unfolding the size function of the sort, as it matches on
 *  every constructor of the sort. */
trait SubtermOrder { self =>
  val trees: ast.Trees
  import trees._

  /** The expression `e` with the values of the variables in `bindings`, and without the lets, assumptions,
   *  annotations and casts around it, as well as the selections from tuples that it builds */
  def inlined(e: Expr, bindings: Map[Variable, Expr]): Expr = inlinedWithCasts(e, bindings)._1

  /** The inlined expression, with the conditions of the casts that it removes */
  private def inlinedWithCasts(e: Expr, bindings: Map[Variable, Expr]): (Expr, Seq[Expr]) = {
    def rec(e: Expr): (Expr, Seq[Expr]) = e match {
      case v: Variable if bindings.contains(v) => rec(bindings(v))
      case Let(vd, v, b) =>
        val (iv, cv) = rec(v)
        val (ib, cb) = rec(b)
        def subst(e: Expr) = exprOps.replaceFromSymbols(Map(vd -> iv), e)
        (subst(ib), cv ++ cb.map(subst))
      case Annotated(b, _) => rec(b)
      case Assume(_, b) => rec(b)
      // Casts are checked separately, and their conditions hold where the cast value is used
      case Assert(cond, _, b) =>
        val (ib, cb) = rec(b)
        (ib, cb :+ cond)
      case TupleSelect(t, i) => rec(t) match {
        case (Tuple(es), ct) =>
          val (ie, ce) = rec(es(i - 1))
          (ie, ct ++ ce)
        case (it, ct) => (TupleSelect(it, i).copiedFrom(e), ct)
      }
      case _ => (e, Seq())
    }
    rec(e)
  }

  /** When `callee` is a selection from `current` through fields of the sort of `tpe`, the constructor tests
   *  that make it a strict subterm of `current`.
   *
   *  Only fields declared with the type of the sort itself, or within tuples, lead to subterms, although
   *  the subterm order on all values is well-founded. Measure inference replaces by their size the
   *  measures that some call doesn't pass a subterm of, and the size of a sort doesn't count the other
   *  fields (as fields whose type is a type parameter). Through these fields, a subterm is also smaller by
   *  size, so that the measures of ADT type that stay values could also be replaced by their size.
   *
   *  The variables bound in `bindings` (by the path, as scrutinees or parameters of inlined functions) are
   *  replaced by their values. With `otherRoots`, the selections may start from another variable, which
   *  the path then equates to `current`. */
  def subterm(tpe: ADTType, callee: Expr, current: Expr, bindings: Map[Variable, Expr], otherRoots: Boolean)
             (using symbols: Symbols): Option[Expr] = {
    import symbols.{given, _}
    val sort = tpe.getSort.definition
    val sortType = ADTType(sort.id, sort.typeArgs)

    // The conditions of the casts in the selections, which hold as the selections are evaluated
    val casts = scala.collection.mutable.ListBuffer.empty[Expr]
    def inlined(e: Expr): Expr = {
      val (ie, conds) = inlinedWithCasts(e, bindings)
      casts ++= conds
      ie
    }

    // The root of the selections, the declared type of the selected value, and the constructor tests
    def selections(e: Expr): Option[(Expr, Type, Seq[Expr])] = e match {
      case sel @ ADTSelector(b, selector) =>
        val base = inlined(b)
        selections(base).collect {
          case (root, `sortType`, tests) =>
            val cons = sel.constructor.definition
            val field = cons.fields.find(_.id == selector).get
            (root, unrefined(field.tpe), tests :+ IsConstructor(base, cons.id).copiedFrom(sel))
        }
      case TupleSelect(base, i) => selections(inlined(base)).collect {
        case (root, TupleType(tps), tests) => (root, unrefined(tps(i - 1)), tests)
      }
      case _ => unrefined(e.getType) match {
        case ADTType(sort.id, _) => Some((e, sortType, Seq()))
        case _ => None
      }
    }

    val root = inlined(current)
    selections(inlined(callee)).collect {
      case (r, `sortType`, tests) if tests.nonEmpty && (r == root || (otherRoots && r.isInstanceOf[Variable])) =>
        implies(andJoin(casts.toSeq.distinct),
          andJoin((if (r == root) Seq() else Seq(Equals(r, root).copiedFrom(callee))) ++ tests))
    }
  }
}

object SubtermOrder {
  def apply(t: ast.Trees): SubtermOrder { val trees: t.type } = new SubtermOrder { val trees: t.type = t }
}
