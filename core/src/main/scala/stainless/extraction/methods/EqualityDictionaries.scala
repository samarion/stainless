/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package extraction
package methods

import scala.collection.mutable.{Map => MutableMap}

/** Scala's `==` on a value whose type holds a class that defines `equals` is not the equality of
 *  the logic, also when the class is only reached through a type parameter:
 *
 * {{{
 * def contains[A](xs: List[A], x: A): Boolean = xs match {
 *   case Nil() => false
 *   case Cons(h, t) => h == x || contains(t, x)
 * }
 * }}}
 *
 * calls `Identifier.equals` once `A` is `Identifier`. This phase finds, over the whole program,
 * the type parameters that are compared with `==` (directly or through a call) and that are
 * instantiated somewhere with a type whose equality is not the one of the logic. The functions of
 * these type parameters take a dictionary, a record of functions
 *
 * {{{
 * case class Eq[A](eqv: (A, A) => Boolean) {
 *   require(forall((x: A) => eqv(x, x)))
 * }
 * }}}
 *
 * and their `==` becomes a call to `eqv`. The other type parameters are left alone, so a
 * program without `equals` is not changed.
 *
 * The `==` of a class that doesn't define `equals` is the equality of its fields. When a field
 * has such a type, it is a call to a function that is generated for the class hierarchy:
 *
 * {{{
 * def ListEqv[A](eq: Eq[A], x: List[A], y: List[A]): Boolean = {
 *   x.isInstanceOf[Cons[A]] && y.isInstanceOf[Cons[A]] && eq.eqv(x.head, y.head) && ListEqv(eq, x.tail, y.tail) ||
 *   x.isInstanceOf[Nil[A]] && y.isInstanceOf[Nil[A]]
 * }.ensuring(res => x == y ==> res)
 * }}}
 *
 * whose postcondition states that equality in the logic implies `==`. This is what makes the
 * dictionaries of such types satisfy the invariant of `Eq`.
 *
 * Sets, bags, maps, arrays and functions are compared as in the logic.
 */
trait EqualityDictionaries extends ExtractionPipeline {
  val s: Trees
  val t: s.type
  import s._

  // The identifiers of the generated definitions are kept across extractions
  private val eqClass = ast.SymbolIdentifier("stainless.internal.Eq")
  private val eqTparam = TypeParameter.fresh("A")
  private val eqvField = ast.SymbolIdentifier("stainless.internal.Eq.eqv")
  private val eqInvariant = ast.SymbolIdentifier("stainless.internal.Eq.inv")
  private val formalEq = ast.SymbolIdentifier("stainless.internal.formalEq")
  private val formalEqTparam = TypeParameter.fresh("A")

  private val eqvIds: MutableMap[Identifier, Identifier] = MutableMap.empty
  private val eqvTparams: MutableMap[(Identifier, Int), TypeParameter] = MutableMap.empty
  private val dictIds: MutableMap[Identifier, Identifier] = MutableMap.empty

  private def eqvId(root: ClassDef): Identifier = synchronized {
    eqvIds.getOrElseUpdate(root.id, ast.SymbolIdentifier(root.id.name + "Eqv"))
  }

  private def eqvTparam(root: ClassDef, i: Int): TypeParameter = synchronized {
    eqvTparams.getOrElseUpdate((root.id, i), TypeParameter.fresh(root.typeArgs(i).id.name))
  }

  private def dictId(tp: TypeParameter): Identifier = synchronized {
    dictIds.getOrElseUpdate(tp.id, FreshIdentifier("eq" + tp.id.name))
  }

  private def eqType(tpe: Type): ClassType = ClassType(eqClass, Seq(tpe))

  override def invalidate(id: Identifier): Unit = ()

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    given s.Symbols = symbols

    def isUserEquals(fd: FunDef): Boolean =
      fd.isMethod && fd.id.name == "equals" && fd.params.map(_.tpe) == Seq(AnyType()) && fd.tparams.isEmpty &&
      fd.returnType == BooleanType() && !fd.flags.contains(Synthetic)

    val equalsMethods: Map[Identifier, FunDef] = symbols.functions.values.toSeq.collect {
      case fd if isUserEquals(fd) => fd.flags.collectFirst { case IsMethodOf(cid) => cid }.get -> fd
    }.toMap

    // A program without `equals` only has the equality of the logic
    if (equalsMethods.isEmpty) return (symbols, ExtractionSummary.NoSummary)

    def equalsOf(cd: ClassDef): Option[FunDef] =
      (cd +: cd.ancestors.map(_.cd)).collectFirst { case c if equalsMethods.contains(c.id) => equalsMethods(c.id) }

    /** The parts of a type that decide whether its `==` is the equality of the logic:
      * the type parameters and the classes with `equals` that `==` reaches. */
    def leaves(tpe: Type, seen: Set[ClassType] = Set.empty): Set[Type] = tpe match {
      case tp: TypeParameter => Set(tp)
      case ct: ClassType if seen(ct) => Set.empty
      case ct: ClassType => ct.lookupClass match {
        case Some(tcd) if equalsOf(tcd.cd).nonEmpty => Set(ct)
        case Some(tcd) => (tcd +: tcd.descendants).flatMap(_.fields).flatMap(vd => leaves(vd.getType, seen + ct)).toSet
        case None => Set.empty
      }
      case TupleType(tps) => tps.flatMap(leaves(_, seen)).toSet
      case _ => Set.empty
    }

    def typeParams(tpe: Type): Set[TypeParameter] = leaves(tpe).collect { case tp: TypeParameter => tp }

    def comparedType(lhs: Expr, rhs: Expr): Type = symbols.leastUpperBound(lhs.getType, rhs.getType)

    val functions = symbols.functions.values.toSeq

    // The instantiations in each function: the type parameters of the functions it calls and
    // of the classes of the methods it calls, with their type arguments
    val calls: Map[Identifier, Seq[(Seq[TypeParameter], Seq[Type])]] = functions.map { fd =>
      fd.id -> exprOps.collect[(Seq[TypeParameter], Seq[Type])] {
        case FunctionInvocation(id, tps, _) => Set(symbols.getFunction(id).typeArgs -> tps)
        case MethodInvocation(rec, id, tps, _) =>
          val callee = symbols.getFunction(id)
          val cd = symbols.getClass(callee.flags.collectFirst { case IsMethodOf(cid) => cid }.get)
          val classArgs = rec.getType match {
            case ct: ClassType => ct.lookupClass.flatMap(tcd => (tcd +: tcd.ancestors).find(_.cd == cd)).map(_.tps)
            case _ => None
          }
          Set((callee.typeArgs ++ cd.typeArgs) -> (tps ++ classArgs.getOrElse(cd.typeArgs)))
        case _ => Set.empty
      } (fd.fullBody).toSeq
    }.toMap

    // The type parameters that are compared, directly or through a call
    val demanded: Set[TypeParameter] = {
      val direct: Set[TypeParameter] = functions.flatMap { fd =>
        exprOps.collect[TypeParameter] {
          case Equals(lhs, rhs) => typeParams(comparedType(lhs, rhs))
          case _ => Set.empty
        } (fd.fullBody)
      }.toSet

      inox.utils.fixpoint { (demanded: Set[TypeParameter]) =>
        demanded ++ functions.flatMap { fd =>
          calls(fd.id).flatMap { case (tparams, tps) =>
            (tparams zip tps).collect { case (tp, tpe) if demanded(tp) => typeParams(tpe) }.flatten
          }
        }
      } (direct)
    }

    def isFormal(tpe: Type, marked: Set[TypeParameter]): Boolean = leaves(tpe).forall {
      case tp: TypeParameter => !marked(tp)
      case _ => false
    }

    // The demanded type parameters that are instantiated with a type whose `==` is not formal
    val marked: Set[TypeParameter] = inox.utils.fixpoint { (marked: Set[TypeParameter]) =>
      marked ++ functions.flatMap { fd =>
        calls(fd.id).flatMap { case (tparams, tps) =>
          (tparams zip tps).collect { case (tp, tpe) if demanded(tp) && !isFormal(tpe, marked) => tp }
        }
      }
    } (Set.empty[TypeParameter])

    val functionTparams: Set[TypeParameter] = functions.flatMap(_.typeArgs).toSet
    for (tp <- marked if !functionTparams(tp)) {
      throw MethodsException(tp, s"Equality on the class type parameter ${tp.id.name} is not supported yet " +
        "when it is instantiated with a type that defines `equals`")
    }

    for (fd <- functions if fd.isMethod && fd.typeArgs.exists(marked) &&
         (symbols.getClass(fd.flags.collectFirst { case IsMethodOf(cid) => cid }.get).descendants.nonEmpty ||
          symbols.getClass(fd.flags.collectFirst { case IsMethodOf(cid) => cid }.get).parents.nonEmpty)) {
      throw MethodsException(fd, s"Equality on a type parameter of the method ${fd.id.name} is not supported yet " +
        "in a class hierarchy when it is instantiated with a type that defines `equals`")
    }

    var changed = false
    val generated: MutableMap[Identifier, Option[FunDef]] = MutableMap.empty

    def rootOf(tcd: TypedClassDef): TypedClassDef = tcd.ancestors.lastOption.getOrElse(tcd)

    /** The type parameters of a class hierarchy that its equality takes a dictionary for. */
    def eqvParams(root: ClassDef): Seq[Int] = {
      val tps = typeParams(ClassType(root.id, root.typeArgs))
      root.typeArgs.indices.filter(i => tps(root.typeArgs(i)))
    }

    class Rewriter(dicts: Map[TypeParameter, Variable], inRoots: Set[Identifier])
      extends ConcreteOOSelfTreeTransformer(s, s) {

      def isFormal(tpe: Type): Boolean = leaves(tpe).forall {
        case tp: TypeParameter => !dicts.contains(tp)
        case _ => false
      }

      private def bind(e: Expr)(body: Variable => Expr): Expr = e match {
        case v: Variable => body(v)
        case _ =>
          val vd = ValDef.fresh("x", e.getType).copiedFrom(e)
          Let(vd, e, body(vd.toVariable)).copiedFrom(e)
      }

      /** The `==` of two values of a type, which are already transformed. */
      def equality(tpe: Type, lhs: Expr, rhs: Expr): Expr = if (isFormal(tpe)) Equals(lhs, rhs) else {
        changed = true
        tpe match {
          case tp: TypeParameter =>
            Application(ClassSelector(dicts(tp), eqvField), Seq(lhs, rhs))

          case ct: ClassType =>
            val tcd = ct.tcd
            equalsOf(tcd.cd) match {
              case Some(fd) => MethodInvocation(lhs, fd.id, Seq.empty, Seq(rhs))
              case None =>
                val root = rootOf(tcd)
                if (root.tps.contains(Untyped) || root.descendants.exists(_.tps.contains(Untyped)))
                  throw MethodsException(ct, s"Equality on class ${ct.id.name} is not supported yet, " +
                    "as its hierarchy instantiates a parent at a specific type")
                generate(root.cd)
                FunctionInvocation(eqvId(root.cd), root.tps,
                  eqvParams(root.cd).map(i => dictionary(root.tps(i))) ++ Seq(lhs, rhs))
            }

          case TupleType(tps) =>
            bind(lhs) { l => bind(rhs) { r =>
              andJoin(tps.zipWithIndex.map { case (tp, i) =>
                equality(tp, TupleSelect(l, i + 1), TupleSelect(r, i + 1))
              })
            }}

          case _ => Equals(lhs, rhs)
        }
      }

      /** The dictionary of a type. */
      def dictionary(tpe: Type): Expr = tpe match {
        case tp: TypeParameter if dicts.contains(tp) => dicts(tp)
        case _ if isFormal(tpe) =>
          changed = true
          FunctionInvocation(formalEq, Seq(tpe), Seq.empty)
        case _ =>
          for (case ClassType(id, _) <- typeOps.collect[Type] { case ct: ClassType => Set(ct); case _ => Set.empty } (tpe);
               root = rootOf(symbols.getClass(id).typed).cd if inRoots(root.id)) {
            throw MethodsException(tpe, s"Equality on class ${root.id.name} is not supported yet, " +
              s"as it recurses through the type ${tpe.asString(using PrinterOptions())}")
          }
          val (x, y) = (ValDef.fresh("x", tpe), ValDef.fresh("y", tpe))
          ClassConstructor(eqType(tpe), Seq(Lambda(Seq(x, y), equality(tpe, x.toVariable, y.toVariable))))
      }

      override def transform(e: Expr): Expr = e match {
        case Equals(lhs, rhs) =>
          equality(comparedType(lhs, rhs), transform(lhs), transform(rhs)).copiedFrom(e)

        case FunctionInvocation(id, tps, args) if symbols.getFunction(id).typeArgs.exists(marked) =>
          FunctionInvocation(id, tps.map(transform), args.map(transform) ++
            (symbols.getFunction(id).typeArgs zip tps).collect { case (tp, tpe) if marked(tp) => dictionary(tpe) }
          ).copiedFrom(e)

        case MethodInvocation(rec, id, tps, args) if symbols.getFunction(id).typeArgs.exists(marked) =>
          MethodInvocation(transform(rec), id, tps.map(transform), args.map(transform) ++
            (symbols.getFunction(id).typeArgs zip tps).collect { case (tp, tpe) if marked(tp) => dictionary(tpe) }
          ).copiedFrom(e)

        case _ => super.transform(e)
      }
    }

    /** Generates the equality of a class hierarchy. */
    def generate(root: ClassDef): Unit = if (!generated.contains(root.id)) {
      generated(root.id) = None

      val tparams = root.typeArgs.indices.map(i => eqvTparam(root, i))
      val tcd = root.typed(tparams)
      val tpe = tcd.toType
      val dicts = eqvParams(root).map(i => ValDef.fresh("eq" + tparams(i).id.name, eqType(tparams(i))))
      val (x, y) = (ValDef.fresh("x", tpe), ValDef.fresh("y", tpe))

      val rewriter = new Rewriter(
        (eqvParams(root).map(tparams) zip dicts.map(_.toVariable)).toMap,
        generated.collect { case (id, None) => id }.toSet)

      val body = orJoin((tcd +: tcd.descendants).filterNot(_.cd.isAbstract).map { sub =>
        val subTpe = sub.toType
        andJoin(Seq(IsInstanceOf(x.toVariable, subTpe), IsInstanceOf(y.toVariable, subTpe)) ++ sub.fields.map { vd =>
          rewriter.equality(vd.getType,
            ClassSelector(AsInstanceOf(x.toVariable, subTpe), vd.id),
            ClassSelector(AsInstanceOf(y.toVariable, subTpe), vd.id))
        })
      })

      val res = ValDef.fresh("res", BooleanType())
      val post = Lambda(Seq(res), Implies(Equals(x.toVariable, y.toVariable), res.toVariable))

      generated(root.id) = Some(new FunDef(
        eqvId(root),
        tparams.map(TypeParameterDef(_)),
        dicts ++ Seq(x, y),
        BooleanType(),
        exprOps.withPostcondition(body, Some(post)),
        Seq(Derived(None))
      ).copiedFrom(root))
    }

    val newFunctions = functions.map { fd =>
      val dictParams = fd.typeArgs.filter(marked).map(tp => ValDef(dictId(tp), eqType(tp)).copiedFrom(fd))
      val rewriter = new Rewriter((fd.typeArgs.filter(marked) zip dictParams.map(_.toVariable)).toMap, Set.empty)
      // `equals` itself and its postcondition compare `this` and `that` as in the logic
      if (isUserEquals(fd)) fd
      else fd.copy(
        params = fd.params ++ dictParams,
        fullBody = rewriter.transform(fd.fullBody)
      ).copiedFrom(fd)
    }

    if (!changed) (symbols, ExtractionSummary.NoSummary) else {
      val eqDef = new ClassDef(
        eqClass,
        Seq(TypeParameterDef(eqTparam)),
        Seq.empty,
        Seq(ValDef(eqvField, FunctionType(Seq(eqTparam, eqTparam), BooleanType()))),
        Seq(Synthetic)
      )

      // Equality in the logic implies the equality of the dictionary
      val invariant = {
        val x = ValDef.fresh("x", eqTparam)
        new FunDef(
          eqInvariant, Seq.empty, Seq.empty, BooleanType(),
          Forall(Seq(x), Application(ClassSelector(This(eqType(eqTparam)), eqvField), Seq(x.toVariable, x.toVariable))),
          Seq(IsInvariant, IsMethodOf(eqClass), Synthetic)
        )
      }

      val formalEqDef = {
        val (x, y) = (ValDef.fresh("x", formalEqTparam), ValDef.fresh("y", formalEqTparam))
        new FunDef(
          formalEq, Seq(TypeParameterDef(formalEqTparam)), Seq.empty, eqType(formalEqTparam),
          ClassConstructor(eqType(formalEqTparam), Seq(Lambda(Seq(x, y), Equals(x.toVariable, y.toVariable)))),
          Seq(Synthetic)
        )
      }

      val newSymbols = NoSymbols
        .withFunctions(newFunctions ++ generated.values.flatten ++ Seq(invariant, formalEqDef))
        .withClasses(symbols.classes.values.toSeq :+ eqDef)
        .withSorts(symbols.sorts.values.toSeq)
        .withTypeDefs(symbols.typeDefs.values.toSeq)

      (newSymbols, ExtractionSummary.NoSummary)
    }
  }
}

object EqualityDictionaries {
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type)(using override val context: inox.Context)
      extends EqualityDictionaries
    new Impl(trees, trees)
  }
}
