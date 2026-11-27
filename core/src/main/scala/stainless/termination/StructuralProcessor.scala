/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.annotation.tailrec

/** Finds structural measures: parameters of each function of the problem, of the same sorts for all
 *  functions, that decrease lexicographically by the subterm order (see [[SubtermOrder]]) in every call
 *  between these functions: the callee's parameter is a subterm of the caller's for some component, and
 *  the same value for the components before it. These measures are the parameters themselves, which the
 *  type checker compares by the subterm order instead of the size of their sort. A single function whose
 *  recursive calls pass subtrees of a parameter otherwise gets the size of this parameter as measure. */
class StructuralProcessor(override val checker: ProcessingPipeline)
                         // Alias for checker, as we cannot use it to define ordering
                         (override val chker: checker.type)
                         (override val ordering: OrderingRelation & Strengthener & RelationBuilder {
                           val checker: chker.type
                         })
  extends OrderingProcessor("Structural Processor", checker, ordering) {

  def this(chker: ProcessingPipeline,
           ordering: OrderingRelation & Strengthener & RelationBuilder {
             val checker: chker.type
           }) =
    this(chker)(chker)(ordering)

  import checker._
  import checker.context._
  import checker.program.trees._
  import checker.program.symbols.{given, _}
  import ordering._

  private val subterms = SubtermOrder(checker.program.trees)

  /** The number of choices of parameters that we try for a problem */
  private val maxChoices = 256

  private def isSubtreeOf(expr: Expr, v: Variable): Boolean = {
    @tailrec
    def rec(e: Expr, fst: Boolean): Boolean = e match {
      case v2: Variable if v == v2 => !fst
      case ADTSelector(cc, _)      => rec(cc, false)
      case Annotated(e, _)         => rec(e, fst)
      case _                       => false
    }
    rec(expr, true)
  }

  /** The longest lexicographic measures that we try */
  private val maxComponents = 3

  /** Parameters of each function, of the same sorts, which decrease lexicographically by the subterm order
   *  in every call: some parameter decreases while the ones before it are passed unchanged */
  private def structuralMeasures(fds: Seq[FunDef], calls: Seq[Relation]): Option[Map[FunDef, Seq[Variable]]] = {
    type Choice = Map[FunDef, Seq[(Variable, ADTType)]]

    def adtParams(fd: FunDef): Seq[(Variable, ADTType)] = fd.params.map(_.toVariable).flatMap { v =>
      unrefined(v.tpe) match {
        case adt: ADTType => Some((v, adt))
        case _ => None
      }
    }

    // The sequences of distinct parameters of `fd` with the given sorts
    def paramSeqs(fd: FunDef, sorts: Seq[Identifier]): Seq[Seq[(Variable, ADTType)]] =
      sorts.foldLeft(Seq(Seq.empty[(Variable, ADTType)])) { (seqs, sort) =>
        for (seq <- seqs; p <- adtParams(fd) if p._2.id == sort && !seq.contains(p)) yield seq :+ p
      }

    def decreases(choice: Choice): Boolean = calls.forall {
      case Relation(fd, path, fi @ FunctionInvocation(_, _, args), _) =>
        val bindings = path.bindings.map { case (vd, e) => vd.toVariable -> e }.toMap
        val callee = fi.tfd.fd
        val components = (choice(fd) zip choice(callee)).map { case ((current, tpe), (param, _)) =>
          (current, tpe, args(callee.params.indexWhere(_.id == param.id)))
        }
        components.indices.exists { i =>
          components.take(i).forall { case (current, _, arg) =>
            subterms.inlined(arg, bindings) == subterms.inlined(current, bindings)
          } && {
            val (current, tpe, arg) = components(i)
            subterms.subterm(tpe, arg, current, bindings, otherRoots = false).isDefined
          }
        }
    }

    // The sequences of sorts of the measures, from the parameters of the first function
    val sortSeqs = (1 to maxComponents).iterator.flatMap { k =>
      adtParams(fds.head).combinations(k).flatMap(_.permutations).map(_.map(_._2.id)).distinct
    }

    sortSeqs.flatMap { sorts =>
      val candidates = fds.map(fd => fd -> paramSeqs(fd, sorts))
      if (candidates.exists(_._2.isEmpty) || candidates.map(_._2.size.toLong).product > maxChoices) None
      else {
        val choices = candidates.foldLeft(Seq(Map.empty: Choice)) {
          case (choices, (fd, seqs)) => for (choice <- choices; seq <- seqs) yield choice + (fd -> seq)
        }
        choices.find(decreases).map(_.view.mapValues(_.map(_._1)).toMap)
      }
    }.nextOption()
  }

  def run(problem: Problem) = timers.termination.processors.recursion.run {
    val fds = problem.funDefs
    val relations = fds.flatMap(getRelations)
    val (calls, others) = relations.partition {
      case Relation(_, _, fi, _) => problem.funSet(fi.tfd.fd)
    }

    val noGuarantees = others.exists {
      case Relation(_, _, fi, _) => !checker.terminates(fi.tfd.fd).isGuaranteed
    }

    def cleared(measures: Map[FunDef, Option[Expr]]) = {
      measures.foreach { case (fd, measure) => measure.foreach(m => measureCache.add(fd -> m)) }
      val inductiveLemmas = Some((ordering.getPostconditions, ordering.insertedApps))
      Some(fds.map(fd => Cleared(fd, measures(fd), inductiveLemmas)))
    }

    if (noGuarantees) {
      None
    } else if (calls.isEmpty) {
      cleared(fds.map(_ -> None).toMap)
    } else (
      // The measures of a problem must have the same type, so a measure given by the user rules them out
      if (fds.exists(_.measure.isDefined)) None else structuralMeasures(fds, calls)
    ) match {
      case Some(measures) =>
        cleared(measures.view.mapValues(params => Some(tupleWrap(params))).toMap)

      case None if fds.size == 1 =>
        val funDef = fds.head
        // The measure is the size of a parameter of which every recursive call passes a subtree, which
        // also covers subtrees through fields of other sorts
        funDef.params.find { arg =>
          calls.forall {
            case Relation(_, path, FunctionInvocation(_, _, args), _) =>
              args(funDef.params.indexOf(arg)) match {
                // handle case class deconstruction in match expression!
                case v: Variable =>
                  path.bindings.exists {
                    case (vd, ccs) if vd.toVariable == v => isSubtreeOf(ccs, arg.toVariable)
                    case _                               => false
                  }
                case expr =>
                  isSubtreeOf(expr, arg.toVariable)
              }
          }
        }.flatMap(p => cleared(Map(funDef -> Some(ordering.measure(Seq(p.toVariable))))))

      case None =>
        None
    }
  }
}
