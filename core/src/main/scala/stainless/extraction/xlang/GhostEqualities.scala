/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package xlang

/** Makes ghost comparisons between values that can contain functions extensional.
  *
  * Functions can't be compared, so Inox rejects `==` on types that contain them. In ghost code,
  * such comparisons become extensional equalities (see [[inox.ast.Expressions.ExtEquals]]), under
  * which functions are equal when they agree on every input. The bodies of quantifiers count as
  * ghost code, but other specifications don't, since they are executed. Non-ghost comparisons are
  * left as they are, and [[TreeSanitizer]] rejects those that compare functions.
  */
object GhostEqualities {
  import trees._

  /** Whether values of type `tpe` can contain functions, including through the fields of classes.
    * Values of type `Any` can contain functions if `withAny` holds. */
  def containsFunctions(trees: xlang.Trees)(tpe: trees.Type, withAny: Boolean)(using symbols: trees.Symbols): Boolean = {
    import trees._

    def rec(tpe: Type, seen: Set[Identifier]): Boolean = tpe match {
      case _: FunctionType | _: PiType => true
      case AnyType() => withAny
      case _: LocalClassType => true
      // Heap references are compared by reference
      case ct: ClassType if ct.lookupClass.exists(tcd => (tcd +: tcd.ancestors).exists(_.cd.flags.exists(_.name == "anyHeapRef"))) =>
        false
      case ct: ClassType =>
        ct.tps.exists(rec(_, seen)) || (!seen(ct.id) && ct.lookupClass.exists { tcd =>
          (tcd +: tcd.descendants).exists(_.fields.exists(vd => rec(vd.getType, seen + ct.id)))
        })
      case RefinementType(vd, _) => rec(vd.tpe, seen)
      case NAryType(tps, _) => tps.exists(rec(_, seen))
    }

    rec(tpe, Set.empty)
  }

  def transform(symbols: Symbols): Symbols = {
    given Symbols = symbols

    val ghostEqualities = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap[Expr, java.lang.Boolean])

    class Collector(override val trees: xlang.trees.type)(using override val symbols: Symbols) extends GhostTraverser {
      import trees._

      // Comparisons on type parameters become extensional too, so that ghost code doesn't
      // require its type parameters to admit equality
      private def needsExtensionality(tpe: Type): Boolean =
        containsFunctions(trees)(tpe, withAny = true) || typeOps.typeParamsOf(tpe).nonEmpty

      override def traverse(e: Expr, ctx: GhostContext): Unit = e match {
        case Equals(lhs, rhs) if ctx.isGhost && (needsExtensionality(lhs.getType) || needsExtensionality(rhs.getType)) =>
          ghostEqualities.add(e)
          super.traverse(e, ctx)

        // Quantifiers can't be executed, unlike the other specifications
        case _: Forall | _: Choose =>
          super.traverse(e, ctx.withinGhost)

        case _ => super.traverse(e, ctx)
      }
    }

    val collector = new Collector(trees)
    symbols.functions.values.foreach(collector.traverse)

    if (ghostEqualities.isEmpty) symbols
    else {
      class Transformer(override val s: trees.type, override val t: trees.type)
        extends innerclasses.ConcreteTreeTransformer(s, t) {
        override def transform(e: s.Expr): t.Expr = e match {
          case s.Equals(lhs, rhs) if ghostEqualities.contains(e) =>
            t.ExtEquals(transform(lhs), transform(rhs)).copiedFrom(e)
          case _ => super.transform(e)
        }
      }

      val transformer = new Transformer(trees, trees)
      symbols.withFunctions(symbols.functions.values.map(transformer.transform).toSeq)
    }
  }
}
