/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package methods

/** Scala's `==` on a class whose hierarchy defines `equals` is a call to that method,
 *  not the equality of the logic.
 *
 *  For example, in
 *
 * {{{
 * case class Identifier(name: String, globalId: BigInt) {
 *   override def equals(that: Any): Boolean = that match {
 *     case id: Identifier => globalId == id.globalId
 *     case _ => false
 *   }
 * }
 * }}}
 *
 * `x == y` on two identifiers becomes `x.equals(y)`. The method gets the
 * postcondition that it holds when `that` is `this`, so that equality in the logic
 * implies `==`. The converse does not hold in general. The method is also pure.
 * Overrides are held to both, as to any postcondition of the `equals` they override.
 */
class UserEquality(override val s: Trees, override val t: Trees)
                  (using override val context: inox.Context)
  extends oo.CachingPhase
     with oo.NoSummaryPhase
     with IdentitySorts
     with SimpleFunctions
     with oo.IdentityTypeDefs
     with oo.IdentityClasses { self =>

  override protected final val funCache = new ExtractionCache({ (fd, context) =>
    FunctionKey(fd) + SetKey(context.equalsMethods.values.toSet.map(FunctionKey(_)))
  })

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(self.s, self.t)(using symbols)

  protected class TransformerContext(override val s: self.s.type, override val t: self.t.type)
                                    (using val symbols: s.Symbols) extends oo.ConcreteTreeTransformer(s, t) {
    import s._
    import symbols._

    private def isUserEquals(fd: FunDef): Boolean =
      fd.isMethod && fd.id.name == "equals" && fd.params.map(_.tpe) == Seq(AnyType()) && fd.tparams.isEmpty &&
      fd.returnType == BooleanType() && !fd.flags.contains(Synthetic)

    /** The `equals` method that each class defines, if any. */
    val equalsMethods: Map[Identifier, FunDef] = symbols.functions.values.toSeq.collect {
      case fd if isUserEquals(fd) => fd.flags.collectFirst { case IsMethodOf(cid) => cid }.get -> fd
    }.toMap

    /** The `equals` method that `==` calls on a value of type `ct`. */
    private def equalsOf(ct: ClassType, pos: inox.utils.Positioned): Option[FunDef] = {
      val cd = symbols.getClass(ct.id)
      (cd +: cd.ancestors.map(_.cd)).collectFirst {
        case c if equalsMethods.contains(c.id) => equalsMethods(c.id)
      } orElse {
        cd.descendants.find(c => equalsMethods.contains(c.id)).map { sub =>
          throw MethodsException(ct.setPos(pos.getPos),
            s"Class ${cd.id.name} is tested for equality and its subclass ${sub.id.name} defines `equals`, " +
            s"so ${cd.id.name} must define `equals` as well")
        }
      }
    }

    override def transform(e: s.Expr): t.Expr = e match {
      case Equals(lhs, rhs) => lhs.getType match {
        case ct: ClassType => equalsOf(ct, e) match {
          case Some(fd) =>
            t.MethodInvocation(transform(lhs), fd.id, Seq.empty, Seq(transform(rhs))).copiedFrom(e)
          case None => super.transform(e)
        }
        case _ => super.transform(e)
      }

      case _ => super.transform(e)
    }

    override def transform(fd: s.FunDef): t.FunDef = {
      val nfd = super.transform(fd)
      if (!isUserEquals(fd)) nfd else {
        // Equality in the logic implies `equals`
        val cd = fd.getClassDef.get
        val thiss = t.This(t.ClassType(cd.id, cd.typeArgs.map(transform(_))).setPos(fd)).setPos(fd)
        def holdsOnThis(res: t.Expr): t.Expr =
          t.Implies(t.Equals(nfd.params.head.toVariable, thiss).setPos(fd), res).setPos(fd)

        val post = t.exprOps.postconditionOf(nfd.fullBody) match {
          case Some(l @ t.Lambda(Seq(res), body)) =>
            t.Lambda(Seq(res), t.And(body, holdsOnThis(res.toVariable)).copiedFrom(body)).copiedFrom(l)
          case _ =>
            val res = t.ValDef.fresh("res", t.BooleanType().setPos(fd)).setPos(fd)
            t.Lambda(Seq(res), holdsOnThis(res.toVariable)).setPos(fd)
        }

        // `equals` may not mutate its argument, also when a subclass overrides it
        nfd.copy(
          fullBody = t.exprOps.withPostcondition(nfd.fullBody, Some(post)),
          flags = (nfd.flags :+ t.IsPure).distinct
        ).copiedFrom(nfd)
      }
    }
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): (t.FunDef, Unit) =
    (context.transform(fd), ())
}

object UserEquality {
  def apply(ts: Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: ts.type
  } = {
    class Impl(override val s: ts.type, override val t: ts.type) extends UserEquality(s, t)
    new Impl(ts, ts)
  }
}
