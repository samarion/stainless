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
 * case class Eq[A](eqv: (A, A) => Boolean, formal: Boolean) {
 *   require(forall((x: A) => eqv(x, x)))
 * }
 * }}}
 *
 * and their `==` becomes `if (eq.formal) x == y else eq.eqv(x, y)`, where `formal` states that
 * the dictionary is the equality of the logic. The other type parameters are left alone, so a
 * program without `equals` is not changed.
 *
 * A method takes the dictionaries of the type parameters of its class that it compares, so
 * `xs.contains(x)` on a `List[Identifier]` passes the dictionary of `Identifier`. This is not
 * supported yet for class invariants, fields and overridden methods.
 *
 * The library is not verified with the program, and its postconditions were proved for the
 * equality of the logic. The postcondition of a library function that takes dictionaries
 * therefore only holds when they are formal, unless it states what it relies on itself with
 * `formalEquality[T]`, which is the `formal` of the dictionary of `T`.
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
  private val formalField = ast.SymbolIdentifier("stainless.internal.Eq.formal")
  private val eqInvariant = ast.SymbolIdentifier("stainless.internal.Eq.inv")
  private val formalEq = ast.SymbolIdentifier("stainless.internal.formalEq")
  private val formalEqTparam = TypeParameter.fresh("A")

  private val eqvIds: MutableMap[Identifier, Identifier] = MutableMap.empty
  private val eqvTparams: MutableMap[(Identifier, Int), TypeParameter] = MutableMap.empty
  private val dictIds: MutableMap[Identifier, Identifier] = MutableMap.empty

  private def eqvId(root: ClassDef): Identifier = synchronized {
    eqvIds.getOrElseUpdate(root.id, ast.SymbolIdentifier(root.id.name + "Eqv"))
  }

  private val nestedEqvIds: MutableMap[Type, Identifier] = MutableMap.empty

  private def nestedEqvId(tpe: Type, name: String): Identifier = synchronized {
    nestedEqvIds.getOrElseUpdate(tpe, ast.SymbolIdentifier(name))
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

    // `formalEquality[T]` states that `==` on `T` is the equality of the logic
    val formalEquality: Option[Identifier] = symbols.lookup.get[FunDef]("stainless.lang.formalEquality").map(_.id)

    object FormalEquality {
      def unapply(e: Expr): Option[Type] = e match {
        case FunctionInvocation(id, Seq(tpe), Seq()) if formalEquality.contains(id) => Some(tpe)
        case _ => None
      }
    }

    // A program without `equals` only has the equality of the logic
    if (equalsMethods.isEmpty) {
      val functions = symbols.functions.values.toSeq.map { fd =>
        if (!exprOps.exists { case FormalEquality(_) => true case _ => false } (fd.fullBody)) fd
        else fd.copy(fullBody = exprOps.postMap {
          case Implies(FormalEquality(_), rhs) => Some(rhs)
          case e @ FormalEquality(_) => Some(BooleanLiteral(true).copiedFrom(e))
          case _ => None
        } (fd.fullBody)).copiedFrom(fd)
      }

      return (symbols.withFunctions(functions), ExtractionSummary.NoSummary)
    }

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

    def classOf(fd: FunDef): Option[ClassDef] =
      fd.flags.collectFirst { case IsMethodOf(cid) => symbols.getClass(cid) }

    /** The type parameters of the class of a method. */
    def classTparams(fd: FunDef): Seq[TypeParameter] = classOf(fd).toSeq.flatMap(_.typeArgs)

    /** The type arguments of the class of a method for a receiver. */
    def classArgs(rec: Expr, callee: FunDef): Seq[Type] = {
      val cd = classOf(callee).get
      (rec.getType match {
        case ct: ClassType => ct.lookupClass.flatMap(tcd => (tcd +: tcd.ancestors).find(_.cd == cd)).map(_.tps)
        case _ => None
      }).getOrElse(cd.typeArgs)
    }

    // The instantiations in each function: the type parameters of the functions it calls and
    // of the classes of the methods it calls, with their type arguments
    val calls: Map[Identifier, Seq[(Identifier, Seq[TypeParameter], Seq[Type])]] = functions.map { fd =>
      fd.id -> exprOps.collect[(Identifier, Seq[TypeParameter], Seq[Type])] {
        case FunctionInvocation(id, tps, _) => Set((id, symbols.getFunction(id).typeArgs, tps))
        case MethodInvocation(rec, id, tps, _) =>
          val callee = symbols.getFunction(id)
          Set((id, callee.typeArgs ++ classTparams(callee), tps ++ classArgs(rec, callee)))
        case _ => Set.empty
      } (fd.fullBody).toSeq
    }.toMap

    // The type parameters that are compared, directly or through a call
    val demanded: Set[TypeParameter] = {
      val direct: Set[TypeParameter] = functions.flatMap { fd =>
        exprOps.collect[TypeParameter] {
          case Equals(lhs, rhs) => typeParams(comparedType(lhs, rhs))
          case FormalEquality(tpe) => typeParams(tpe)
          case _ => Set.empty
        } (fd.fullBody)
      }.toSet

      inox.utils.fixpoint { (demanded: Set[TypeParameter]) =>
        demanded ++ functions.flatMap { fd =>
          calls(fd.id).flatMap { case (_, tparams, tps) =>
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
        calls(fd.id).flatMap { case (_, tparams, tps) =>
          (tparams zip tps).collect { case (tp, tpe) if demanded(tp) && !isFormal(tpe, marked) => tp }
        }
      }
    } (Set.empty[TypeParameter])

    // The type parameters of its class that a method takes a dictionary for: those that it
    // compares, directly or through a call
    val needed: Map[Identifier, Set[TypeParameter]] = {
      def ofClass(fd: FunDef, tps: Set[TypeParameter]): Set[TypeParameter] = tps & classTparams(fd).toSet & marked

      val direct: Map[Identifier, Set[TypeParameter]] = functions.map { fd =>
        fd.id -> ofClass(fd, exprOps.collect[TypeParameter] {
          case Equals(lhs, rhs) => typeParams(comparedType(lhs, rhs))
          case FormalEquality(tpe) => typeParams(tpe)
          case _ => Set.empty
        } (fd.fullBody))
      }.toMap

      inox.utils.fixpoint { (needed: Map[Identifier, Set[TypeParameter]]) =>
        functions.map { fd =>
          fd.id -> (needed(fd.id) ++ ofClass(fd, calls(fd.id).flatMap { case (id, tparams, tps) =>
            val callee = symbols.getFunction(id)
            (tparams zip tps).collect {
              case (tp, tpe) if marked(tp) && (callee.typeArgs.contains(tp) || needed(id)(tp)) => typeParams(tpe)
            }.flatten
          }.toSet))
        }.toMap
      } (direct)
    }

    /** The type parameters that a function takes a dictionary for. */
    def dictTparams(fd: FunDef): Seq[TypeParameter] =
      fd.typeArgs.filter(marked) ++ classTparams(fd).filter(needed(fd.id))

    def instance(tp: TypeParameter): String = functions.flatMap { fd =>
      calls(fd.id).flatMap { case (_, tparams, tps) =>
        (tparams zip tps).collect { case (`tp`, tpe) if typeParams(tpe).isEmpty && !isFormal(tpe, marked) => tpe }
      }
    }.headOption.map(tpe => s" (as ${tpe.asString(using PrinterOptions())} is)").getOrElse("")

    for (fd <- functions; tp <- needed(fd.id).headOption) {
      val symbol = fd.id.asInstanceOf[SymbolIdentifier].symbol
      val family = functions.count(f => f.isMethod && f.id.asInstanceOf[SymbolIdentifier].symbol == symbol)
      val kind =
        if (fd.flags.contains(IsInvariant)) Some("a class invariant")
        else if (fd.flags.exists { case IsAccessor(_) => true case _ => false }) Some("a field")
        else if (family > 1) Some(s"the method ${fd.id.name}, which is overridden")
        else None

      for (kind <- kind) throw MethodsException(fd,
        s"Equality on the class type parameter ${tp.id.name} in $kind is not supported yet " +
        s"when it is instantiated with a type that defines `equals`${instance(tp)}")
    }

    for (fd <- functions if fd.isMethod && fd.typeArgs.exists(marked) &&
         (symbols.getClass(fd.flags.collectFirst { case IsMethodOf(cid) => cid }.get).descendants.nonEmpty ||
          symbols.getClass(fd.flags.collectFirst { case IsMethodOf(cid) => cid }.get).parents.nonEmpty)) {
      throw MethodsException(fd, s"Equality on a type parameter of the method ${fd.id.name} is not supported yet " +
        "in a class hierarchy when it is instantiated with a type that defines `equals`")
    }

    var changed = false
    val generated: MutableMap[Identifier, Option[FunDef]] = MutableMap.empty
    val generatedNested: MutableMap[Type, FunDef] = MutableMap.empty

    def rootOf(tcd: TypedClassDef): TypedClassDef = tcd.ancestors.lastOption.getOrElse(tcd)

    /** The type parameters of a class hierarchy that its equality takes a dictionary for. */
    def eqvParams(root: ClassDef): Seq[Int] = {
      val tps = typeParams(ClassType(root.id, root.typeArgs))
      root.typeArgs.indices.filter(i => tps(root.typeArgs(i)))
    }

    class Rewriter(dicts: Map[TypeParameter, Variable], inRoots: Set[Identifier])
      extends ConcreteOOSelfTreeTransformer(s, s) {

      def isFormal(tpe: Type): Boolean = leaves(tpe).forall {
        case tp: TypeParameter if dicts.contains(tp) => false
        case tp: TypeParameter if marked(tp) =>
          throw MethodsException(tp, s"Equality on the type parameter ${tp.id.name} is not supported here yet " +
            "when it is instantiated with a type that defines `equals`")
        case tp: TypeParameter => true
        case _ => false
      }

      /** Whether a type holds a class whose equality is being generated. */
      private def inProgress(tpe: Type): Boolean = typeOps.exists {
        case ClassType(id, _) => inRoots(rootOf(symbols.getClass(id).typed).cd.id)
        case _ => false
      } (tpe)

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
            // A dictionary states whether it is the equality of the logic, which is what the
            // specifications that relate `==` to sets and maps rely on
            IfExpr(ClassSelector(dicts(tp), formalField), Equals(lhs, rhs),
              Application(ClassSelector(dicts(tp), eqvField), Seq(lhs, rhs)))

          case ct: ClassType =>
            val tcd = ct.tcd
            equalsOf(tcd.cd) match {
              case Some(fd) => MethodInvocation(lhs, fd.id, Seq.empty, Seq(rhs))
              case None =>
                val root = rootOf(tcd)
                if (root.tps.contains(Untyped) || root.descendants.exists(_.tps.contains(Untyped)))
                  throw MethodsException(ct, s"Equality on class ${ct.id.name} is not supported yet, " +
                    "as its hierarchy instantiates a parent at a specific type")
                if (root.tps.exists(inProgress)) {
                  // The class recurses through this type, so it can't take a dictionary of the class
                  val nested = generateNested(root, dicts.keySet, inRoots)
                  FunctionInvocation(nested.id, nested.typeArgs,
                    nested.typeArgs.filter(dicts.contains).map(dicts) ++ Seq(lhs, rhs))
                } else {
                  generate(root.cd)
                  FunctionInvocation(eqvId(root.cd), root.tps,
                    eqvParams(root.cd).map(i => dictionary(root.tps(i))) ++ Seq(lhs, rhs))
                }
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
          if (inProgress(tpe)) {
            throw MethodsException(tpe, "Equality on a class that recurses through the type " +
              s"${tpe.asString(using PrinterOptions())} is not supported yet")
          }
          val (x, y) = (ValDef.fresh("x", tpe), ValDef.fresh("y", tpe))
          ClassConstructor(eqType(tpe), Seq(Lambda(Seq(x, y), equality(tpe, x.toVariable, y.toVariable)), BooleanLiteral(false)))
      }

      /** Whether the `==` of a type is the equality of the logic. */
      def formality(tpe: Type): Expr = if (isFormal(tpe)) BooleanLiteral(true) else {
        changed = true
        andJoin(leaves(tpe).toSeq.map {
          case tp: TypeParameter if dicts.contains(tp) => ClassSelector(dicts(tp), formalField)
          case tp: TypeParameter => BooleanLiteral(true)
          case _ => BooleanLiteral(false)
        })
      }

      override def transform(e: Expr): Expr = e match {
        case Implies(FormalEquality(tpe), rhs) if isFormal(tpe) => transform(rhs)
        case FormalEquality(tpe) => formality(tpe).copiedFrom(e)

        case Equals(lhs, rhs) =>
          equality(comparedType(lhs, rhs), transform(lhs), transform(rhs)).copiedFrom(e)

        case FunctionInvocation(id, tps, args) if dictTparams(symbols.getFunction(id)).nonEmpty =>
          val callee = symbols.getFunction(id)
          val tpMap = (callee.typeArgs zip tps).toMap
          FunctionInvocation(id, tps.map(transform), args.map(transform) ++
            dictTparams(callee).map(tp => dictionary(tpMap(tp)))
          ).copiedFrom(e)

        case MethodInvocation(rec, id, tps, args) if dictTparams(symbols.getFunction(id)).nonEmpty =>
          val callee = symbols.getFunction(id)
          val tpMap = ((callee.typeArgs ++ classTparams(callee)) zip (tps ++ classArgs(rec, callee))).toMap
          MethodInvocation(transform(rec), id, tps.map(transform), args.map(transform) ++
            dictTparams(callee).map(tp => dictionary(tpMap(tp)))
          ).copiedFrom(e)

        case ApplyLetRec(_, tparams, _, tps, _)
        if (tparams zip tps).exists { case (tp, tpe) => demanded(tp) && !isFormal(tpe) } =>
          throw MethodsException(e, "Equality on a type parameter of an inner function is not supported yet " +
            "when it is instantiated with a type that defines `equals`")

        case _ => super.transform(e)
      }
    }

    /** Generates the equality of a class hierarchy. */
    def generate(root: ClassDef): Unit = if (!generated.contains(root.id)) {
      generated(root.id) = None
      val tparams = root.typeArgs.indices.map(i => eqvTparam(root, i))
      generated(root.id) = Some(build(eqvId(root), tparams, root.typed(tparams), eqvParams(root).map(tparams),
        generated.collect { case (id, None) => id }.toSet))
    }

    /** Generates the equality of a class hierarchy at the type arguments through which another
      * class recurses, as in `List[Tree[A]]` for the children of a `Tree[A]`. It takes the
      * dictionaries of that class. */
    def generateNested(root: TypedClassDef, dicts: Set[TypeParameter], inRoots: Set[Identifier]): FunDef = {
      val tpe = root.toType
      generatedNested.get(tpe) match {
        case Some(fd) => fd
        case None =>
          val tparams = {
            var seen: Seq[TypeParameter] = Seq.empty
            typeOps.preTraversal { case tp: TypeParameter if !seen.contains(tp) => seen :+= tp; case _ => } (tpe)
            seen
          }
          val id = nestedEqvId(tpe, root.cd.id.name + "Eqv_" + root.tps.flatMap { tp =>
            typeOps.collect[String] { case ClassType(id, _) => Set(id.name); case _ => Set.empty } (tp)
          }.distinct.mkString("_"))

          // The function is registered before its body is built, as the body refers to it
          generatedNested(tpe) = new FunDef(id, tparams.map(TypeParameterDef(_)),
            tparams.filter(dicts).map(tp => ValDef.fresh("eq" + tp.id.name, eqType(tp))) ++
              Seq(ValDef.fresh("x", tpe), ValDef.fresh("y", tpe)),
            BooleanType(), NoTree(BooleanType()), Seq(Derived(None)))
          val fd = build(id, tparams, root, tparams.filter(dicts), inRoots)
          generatedNested(tpe) = fd
          fd
      }
    }

    def build(id: Identifier, tparams: Seq[TypeParameter], tcd: TypedClassDef,
              dictTparams: Seq[TypeParameter], inRoots: Set[Identifier]): FunDef = {
      val root = tcd.cd
      val tpe = tcd.toType
      val dicts = dictTparams.map(tp => ValDef.fresh("eq" + tp.id.name, eqType(tp)))
      val (x, y) = (ValDef.fresh("x", tpe), ValDef.fresh("y", tpe))

      val rewriter = new Rewriter((dictTparams zip dicts.map(_.toVariable)).toMap, inRoots)

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

      new FunDef(
        id,
        tparams.map(TypeParameterDef(_)),
        dicts ++ Seq(x, y),
        BooleanType(),
        exprOps.withPostcondition(body, Some(post)),
        Seq(Derived(None))
      ).copiedFrom(root)
    }

    val newFunctions = functions.map { fd =>
      val dictParams = dictTparams(fd).map(tp => ValDef(dictId(tp), eqType(tp)).copiedFrom(fd))
      val rewriter = new Rewriter((dictTparams(fd) zip dictParams.map(_.toVariable)).toMap, Set.empty)
      // `equals` itself and its postcondition compare `this` and `that` as in the logic
      if (isUserEquals(fd)) fd
      else {
        val body = rewriter.transform(fd.fullBody)
        // The library is not verified with the program, and its postconditions were only proved
        // for the equality of the logic, unless they say what they rely on with `formalEquality`
        val guarded = exprOps.postconditionOf(body) match {
          case Some(post @ Lambda(Seq(res), pred))
          if fd.flags.contains(Library) && dictParams.nonEmpty &&
             !exprOps.exists { case FormalEquality(_) => true case _ => false } (fd.fullBody) =>
            val formal = andJoin(dictParams.map(vd => ClassSelector(vd.toVariable, formalField)))
            exprOps.withPostcondition(body, Some(Lambda(Seq(res), Implies(formal, pred).copiedFrom(pred)).copiedFrom(post)))
          case _ => body
        }
        fd.copy(params = fd.params ++ dictParams, fullBody = guarded).copiedFrom(fd)
      }
    }

    if (!changed) (symbols, ExtractionSummary.NoSummary) else {
      val eqDef = new ClassDef(
        eqClass,
        Seq(TypeParameterDef(eqTparam)),
        Seq.empty,
        Seq(ValDef(eqvField, FunctionType(Seq(eqTparam, eqTparam), BooleanType())), ValDef(formalField, BooleanType())),
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
          ClassConstructor(eqType(formalEqTparam), Seq(Lambda(Seq(x, y), Equals(x.toVariable, y.toVariable)), BooleanLiteral(true))),
          Seq(Synthetic)
        )
      }

      val newSymbols = NoSymbols
        .withFunctions(newFunctions ++ generated.values.flatten ++ generatedNested.values ++ Seq(invariant, formalEqDef))
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
