/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

trait TypeOps extends inox.ast.TypeOps {
  protected val trees: Trees
  import trees._
  import symbols.{given, _}

  def unapplyAccessorResultType(id: Identifier, inType: Type): Option[Type] =
    lookupFunction(id)
      .filter(_.params.size == 1)
      .flatMap { fd =>
        instantiation(fd.params.head.tpe, inType)
          .filter(tpMap => fd.typeArgs forall (tpMap contains _))
          .map(typeOps.instantiateType(fd.returnType, _))
      }

  def patternIsTyped(in: Type, pat: Pattern): Boolean = {
    require(in != Untyped)
    pat match {
      case WildcardPattern(ob) => ob.forall(vd => isSubtypeOf(in, vd.getType))

      case LiteralPattern(ob, lit) =>
        ob.forall(vd => isSubtypeOf(vd.getType, in)) &&
        isSubtypeOf(lit.getType, in)

      case ADTPattern(ob, id, tps, subs) => in.getType match {
        case ADTType(sort, tps2) =>
          tps.map(_.getType) == tps2 &&
          ob.forall(vd => isSubtypeOf(vd.getType, in)) &&
          lookupConstructor(id).exists { cons =>
            cons.sort == sort &&
            cons.fields.size == subs.size &&
            lookupSort(sort).exists(sort => sort.tparams.size == tps.size) &&
            (cons.typed(tps).fields zip subs).forall { case (vd, sub) => patternIsTyped(vd.getType, sub) }
          }
        case _ => false
      }

      case TuplePattern(ob, subs) => in match {
        case TupleType(tps) =>
          tps.size == subs.size &&
          ob.forall(vd => isSubtypeOf(vd.getType, in)) &&
          ((tps zip subs) forall (patternIsTyped(_, _)).tupled)
        case _ => false
      }

      case AlternativePattern(ob, subs) => 
        ob.forall(vd => isSubtypeOf(vd.getType, in)) &&
        (subs exists (patternIsTyped(in, _)))

      case RefinementPattern(underlying, pred) =>
        patternIsTyped(in, underlying) && pred.isTyped

      case up @ UnapplyPattern(ob, recs, id, tps, subs) =>
        ob.forall(vd => isSubtypeOf(vd.getType, in)) &&
        lookupFunction(id).exists(_.tparams.size == tps.size) && {
          val unapp = up.getFunction
          unapp.params.nonEmpty &&
          ob.forall(vd => isSubtypeOf(unapp.params.last.getType, vd.getType)) &&
          (recs zip unapp.params.init).forall { case (r, vd) => isSubtypeOf(r.getType, vd.getType) } &&
          unapp.flags
            .collectFirst { case IsUnapply(isEmpty, get) => (isEmpty, get) }
            .exists { case (isEmpty, get) =>
              unapplyAccessorResultType(isEmpty, unapp.returnType).exists(isSubtypeOf(_, BooleanType())) &&
              unapplyAccessorResultType(get, unapp.returnType).exists {
                case TupleType(tps) =>
                  tps.size == subs.size &&
                  ((tps zip subs) forall patternIsTyped.tupled)
                case tpe if subs.size == 1 =>
                  patternIsTyped(tpe, subs.head)
                case _ => subs.isEmpty
              }
            }
        }
    }
  }

  /** Erases the refinements that values of `tpe` must satisfy, i.e. those in positive positions.
    *
    * The domains of function types are conditions on the callee, so they are kept.
    */
  def erasePositiveRefinements(tpe: Type): Type = tpe match {
    case RefinementType(vd, _) => erasePositiveRefinements(vd.tpe)
    case FunctionType(from, to) => FunctionType(from, erasePositiveRefinements(to)).copiedFrom(tpe)
    case PiType(params, to) => PiType(params, erasePositiveRefinements(to)).copiedFrom(tpe)
    case SigmaType(params, to) =>
      val (newParams, subst) = eraseBinders(params)
      SigmaType(newParams, erasePositiveRefinements(typeOps.replaceFromSymbols(subst, to))).copiedFrom(tpe)
    case NAryType(tps, recons) => recons(tps.map(erasePositiveRefinements))
  }

  /** Erases the positive refinements in the types of `vds`, where each type may refer to the
    * earlier binders, and returns the new binders with the substitution from the old ones.
    */
  private def eraseBinders(vds: Seq[ValDef]): (Seq[ValDef], Map[ValDef, Expr]) =
    vds.foldLeft((Seq.empty[ValDef], Map.empty[ValDef, Expr])) { case ((vds, subst), vd) =>
      val tpe = erasePositiveRefinements(typeOps.replaceFromSymbols(subst, vd.tpe))
      val nvd = if (tpe == vd.tpe) vd else vd.copy(tpe = tpe).copiedFrom(vd)
      (vds :+ nvd, subst + (vd -> nvd.toVariable))
    }

  /** Erases the refinements that `fd`'s parameter types place on its arguments.
    *
    * Stainless checks every call argument against the parameter types with dedicated VCs, so
    * the solver need not prove the refinements in argument positions again. Without them, Inox
    * assumes the function's return type at every call, whatever the arguments. The parameters
    * keep their identifiers.
    */
  def eraseParamRefinements(fd: FunDef): FunDef = {
    val (newParams, subst) = eraseBinders(fd.params)
    if (newParams == fd.params) fd
    else fd.copy(
      params = newParams,
      returnType = typeOps.replaceFromSymbols(subst, fd.returnType),
      fullBody = exprOps.replaceFromSymbols(subst, fd.fullBody)
    ).copiedFrom(fd)
  }

  def replaceKeepPositions(subst: Map[Variable, Expr], tpe: Type): Type = {
    new ConcreteStainlessSelfTreeTransformer {
      override def transform(expr: Expr): Expr = expr match {
        case v: Variable =>
          subst.get(v).map(_.copiedFrom(v)).getOrElse(super.transform(v))
        case _ => super.transform(expr)
      }
    }.transform(tpe)
  }

  protected class Unsolvable extends Exception
  protected def unsolvable = throw new Unsolvable

  /** Collects the constraints that need to be solved for [[unify]].
   * Note: this is an override point. */
  protected def unificationConstraints(t1: Type, t2: Type, free: Seq[TypeParameter]): List[(TypeParameter, Type)] = (t1, t2) match {
    case (adt: ADTType, _) if adt.lookupSort.isEmpty => unsolvable
    case (_, adt: ADTType) if adt.lookupSort.isEmpty => unsolvable

    case _ if t1 == t2 => Nil

    case (adt1: ADTType, adt2: ADTType) if adt1.id == adt2.id =>
      (adt1.tps zip adt2.tps).toList flatMap (p => unificationConstraints(p._1, p._2, free))

    case (rt: RefinementType, _) => unificationConstraints(rt.getType, t2, free)
    case (_, rt: RefinementType) => unificationConstraints(t1, rt.getType, free)

    case (pi: PiType, _) => unificationConstraints(pi.getType, t2, free)
    case (_, pi: PiType) => unificationConstraints(t1, pi.getType, free)

    case (sigma: SigmaType, _) => unificationConstraints(sigma.getType, t2, free)
    case (_, sigma: SigmaType) => unificationConstraints(t1, sigma.getType, free)

    case (tp: TypeParameter, _) if !(typeOps.typeParamsOf(t2) contains tp) && (free contains tp) => List(tp -> t2)
    case (_, tp: TypeParameter) if !(typeOps.typeParamsOf(t1) contains tp) && (free contains tp) => List(tp -> t1)
    case (_: TypeParameter, _) => unsolvable
    case (_, _: TypeParameter) => unsolvable

    case typeOps.Same(NAryType(ts1, _), NAryType(ts2, _)) if ts1.size == ts2.size =>
      (ts1 zip ts2).toList flatMap (p => unificationConstraints(p._1, p._2, free))
    case _ => unsolvable
  }

  /** Solves the constraints collected by [[unificationConstraints]].
   * Note: this is an override point. */
  protected def unificationSolution(const: List[(Type, Type)]): List[(TypeParameter, Type)] = const match {
    case Nil => Nil
    case (tp: TypeParameter, t) :: tl =>
      val replaced = tl map { case (t1, t2) =>
        (typeOps.instantiateType(t1, Map(tp -> t)), typeOps.instantiateType(t2, Map(tp -> t)))
      }
      (tp -> t) :: unificationSolution(replaced)
    case (adt: ADTType, _) :: tl if adt.lookupSort.isEmpty => unsolvable
    case (_, adt: ADTType) :: tl if adt.lookupSort.isEmpty => unsolvable
    case (ADTType(id1, tps1), ADTType(id2, tps2)) :: tl if id1 == id2 =>
      unificationSolution((tps1 zip tps2).toList ++ tl)
    case typeOps.Same(NAryType(ts1, _), NAryType(ts2, _)) :: tl if ts1.size == ts2.size =>
      unificationSolution((ts1 zip ts2).toList ++ tl)
    case _ =>
      unsolvable
  }

  /** Unifies two types, under a set of free variables */
  def unify(t1: Type, t2: Type, free: Seq[TypeParameter]): Option[List[(TypeParameter, Type)]] = {
    try {
      Some(unificationSolution(unificationConstraints(t1, t2, free)))
    } catch {
      case _: Unsolvable => None
    }
  }

}
