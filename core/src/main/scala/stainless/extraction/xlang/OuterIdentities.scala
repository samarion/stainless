/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package xlang

import stainless.ast.SymbolIdentifier

/** Draws the identities of new outer instances from a ghost allocator.
 *
 *  Scala tests outer instances of member classes with reference equality. Instances of classes
 *  with member classes therefore carry a ghost identity, which the frontend initializes with a
 *  placeholder (an `Annotated(NoTree(BigInt), Seq(Annotation("freshIdentity", Seq())))`).
 *
 *  This phase replaces each placeholder with the next value of a ghost counter, held by an
 *  allocator that is passed as a ghost parameter to all functions that construct such instances,
 *  directly or through calls. As the counter only increases, identities drawn from the same
 *  allocator are distinct. For example,
 *
 * {{{
 * def mk(n: BigInt): Trees = new MyTrees(<fresh>, n)
 * def two: (Trees, Trees) = (mk(1), mk(1))
 * }}}
 *
 * becomes
 *
 * {{{
 * def mk(n: BigInt, @ghost alloc: Allocator): Trees = new MyTrees({
 *   @ghost val id = alloc.next
 *   @ghost alloc.next = id + 1
 *   id
 * }, n)
 * def two(@ghost alloc: Allocator): (Trees, Trees) = (mk(1, alloc), mk(1, alloc))
 * }}}
 */
class OuterIdentities(override val s: Trees)(override val t: s.type)
                     (using override val context: inox.Context) extends ExtractionPipeline { self =>
  import s._

  override def invalidate(id: Identifier): Unit = ()

  private val allocatorId = SymbolIdentifier("stainless.internal.Allocator")
  private val nextId = SymbolIdentifier("stainless.internal.Allocator.next")

  private def isFreshIdentity(e: Expr): Boolean = e match {
    case Annotated(NoTree(_), Seq(Annotation("freshIdentity", Seq()))) => true
    case _ => false
  }

  private def callees(fd: FunDef): Set[Identifier] = exprOps.collect[Identifier] {
    case FunctionInvocation(id, _, _) => Set(id)
    case MethodInvocation(_, id, _, _) => Set(id)
    case _ => Set()
  } (fd.fullBody)

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    val allocating0 = symbols.functions.values.filter(fd => exprOps.exists(isFreshIdentity)(fd.fullBody)).map(_.id).toSet
    if (allocating0.isEmpty) return (symbols, ExtractionSummary.NoSummary)

    // Overriding methods share their symbol, and must all take the allocator if one of them does
    val overrides: Map[Identifier, Set[Identifier]] = {
      val bySymbol = symbols.functions.keys.toSeq.collect { case id: SymbolIdentifier => id }.groupBy(_.symbol)
      symbols.functions.keys.map {
        case id: SymbolIdentifier if symbols.functions(id).isMethod => id -> bySymbol(id.symbol).toSet
        case id => id -> Set(id)
      }.toMap
    }

    val calls: Map[Identifier, Set[Identifier]] = symbols.functions.values.map(fd => fd.id -> callees(fd)).toMap

    var allocating = allocating0.flatMap(overrides)
    var changed = true
    while (changed) {
      val next = allocating ++ symbols.functions.keys.filter(id => calls(id).exists(allocating)).flatMap(overrides)
      changed = next.size != allocating.size
      allocating = next
    }

    val allocatorType = ClassType(allocatorId, Seq.empty)
    val allocator = new ClassDef(allocatorId, Seq.empty, Seq.empty, Seq(VarDef(nextId, IntegerType(), Seq(Ghost))), Seq.empty)

    def transform(fd: FunDef): FunDef = {
      val alloc = ValDef.fresh("alloc", allocatorType).copy(flags = Seq(Ghost)).copiedFrom(fd)

      object transformer extends ConcreteOOSelfTreeTransformer(self.s, self.s) {
        private var inLambda = false

        private def checkContext(e: Expr): Unit =
          if (inLambda) context.reporter.fatalError(e.getPos,
            "Stainless does not support constructing instances of classes with member classes within lambdas")

        override def transform(e: Expr): Expr = e match {
          case _ if isFreshIdentity(e) =>
            checkContext(e)
            val id = ValDef.fresh("id", IntegerType()).copy(flags = Seq(Ghost)).copiedFrom(e)
            val sel = ClassSelector(alloc.toVariable, nextId).copiedFrom(e)
            val incr = FieldAssignment(alloc.toVariable, nextId, Plus(id.toVariable, IntegerLiteral(1)).copiedFrom(e)).copiedFrom(e)
            Let(id, sel, Block(Seq(Annotated(incr, Seq(Ghost)).copiedFrom(e)), id.toVariable).copiedFrom(e)).copiedFrom(e)

          case FunctionInvocation(id, tps, args) if allocating(id) =>
            checkContext(e)
            FunctionInvocation(id, tps.map(transform), args.map(transform) :+ alloc.toVariable).copiedFrom(e)

          case MethodInvocation(rec, id, tps, args) if allocating(id) =>
            checkContext(e)
            MethodInvocation(transform(rec), id, tps.map(transform), args.map(transform) :+ alloc.toVariable).copiedFrom(e)

          case l: Lambda =>
            val old = inLambda
            inLambda = true
            try super.transform(l) finally inLambda = old

          case _ => super.transform(e)
        }
      }

      fd.copy(params = fd.params :+ alloc, fullBody = transformer.transform(fd.fullBody))
    }

    val newSymbols = NoSymbols
      .withFunctions(symbols.functions.values.map(fd => if (allocating(fd.id)) transform(fd) else fd).toSeq)
      .withSorts(symbols.sorts.values.toSeq)
      .withClasses(symbols.classes.values.toSeq :+ allocator)
      .withTypeDefs(symbols.typeDefs.values.toSeq)

    (newSymbols, ExtractionSummary.NoSummary)
  }
}

object OuterIdentities {
  def apply(trees: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends OuterIdentities(s)(t)
    new Impl(trees, trees)
  }
}
