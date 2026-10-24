/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package termination

/** Makes the remaining comparisons between values that can't be compared extensional.
  *
  * Inox only admits equality on types that don't contain functions (see
  * [[inox.ast.EqualityTypes]]). User comparisons on other types are either ghost, and already
  * extensional (see [[xlang.GhostEqualities]]), or rejected by [[xlang.TreeSanitizer]]. The ones
  * left were introduced by the extraction phases, for instance between encoded values of type
  * `Any` or heaps, and become extensional equalities too.
  */
class ExtensionalEqualities(override val s: Trees)(override val t: s.type)
                           (using override val context: inox.Context)
  extends CachingPhase
     with NoSummaryPhase
     with SimpleFunctions
     with IdentitySorts { self =>

  import s._

  // Whether a type admits equality depends on the sorts it mentions
  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  protected class TransformerContext(using val symbols: Symbols)
  override protected def getContext(syms: Symbols) = new TransformerContext(using syms)

  override protected def extractFunction(tcontext: TransformerContext, fd: FunDef): (FunDef, Unit) = {
    import tcontext.symbols
    import symbols.given

    // Comparisons also occur in the refinements of parameter and result types
    object transformer extends ConcreteStainlessSelfTreeTransformer {
      override def transform(e: Expr): Expr = super.transform(e) match {
        case eq @ Equals(lhs, rhs) =>
          val tpe = symbols.leastUpperBound(lhs.getType, rhs.getType)
          if (tpe == Untyped || symbols.admitsEquality(tpe)) eq
          else ExtEquals(lhs, rhs).copiedFrom(eq)
        case e2 => e2
      }
    }

    val newFd = fd.copy(
      params = fd.params.map(transformer.transform),
      returnType = transformer.transform(fd.returnType),
      fullBody = transformer.transform(fd.fullBody)
    ).copiedFrom(fd)

    (newFd, ())
  }
}

object ExtensionalEqualities {
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends ExtensionalEqualities(s)(t)
    new Impl(trees, trees)
  }
}
