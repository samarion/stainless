/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import scala.language.implicitConversions

import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.core.CompilationUnitInfo
import dotty.tools.dotc.core.Flags._
import dotty.tools.dotc.core.Symbols._
import dotty.tools.dotc.core.Contexts._
import dotty.tools.io.AbstractFile
import stainless.ast.SymbolIdentifier

import scala.collection.mutable.{ Map => MutableMap, LinkedHashMap }

class SymbolMapping {
  import SymbolMapping._
  import FetchingMode._

  /** Mapping for class invariants: class' id -> inv's id. */
  private val invs = MutableMap[SymbolIdentifier, SymbolIdentifier]()
  private val invSymbol = stainless.ast.Symbol("inv")

  /** Mapping from [[Symbol]] and the stainless identifier. */
  private val s2s = MutableMap[Symbol, SymbolIdentifier]()
  private val s2sAccessor = MutableMap[Symbol, SymbolIdentifier]()
  private val s2sEnumType = MutableMap[Symbol, SymbolIdentifier]()

  /** Returns a mapping from used Tasty root trees to their associated file.
    *
    * Everytime a [[Symbol]] is touched through [[fetch]], we check if it has an
    * associated Tasty file. If it does, we register the symbol's root tree
    * (which is the tree of the compilation unit containing the symbol's
    * definition).
    *
    * We keep this information to later extract compilation units defined in
    * Tasty files, in [[StainlessExtraction.extractTastyUnits]].
    *
    * We key by tree so that each unique tree is extracted exactly once.
    *
    * This a [[LinkedHashMap]] to keep elements in insertion order (there is no
    * efficient immutable equivalent in the Scala standard library).
    *
    * Side-effect: calling this method clears the internal list of used Tasty
    * units.
    */
  def popUsedTastyUnits(): LinkedHashMap[tpd.Tree, AbstractFile] =
    val res = usedTastyUnits
    usedTastyUnits = LinkedHashMap[tpd.Tree, AbstractFile]()
    res

  private var usedTastyUnits = LinkedHashMap[tpd.Tree, AbstractFile]()

  private def maybeRegisterTastyUnit(sym: Symbol)(using Context): Unit = {
    if (sym.tastyInfo.isDefined) {
      val classSym = sym.topLevelClass.asClass
      // Below, `classSym.rootTree` returns the tree read from the Tasty file.
      // It works because we passed the `-Yretain-trees` option to the compiler.
      usedTastyUnits += (classSym.rootTree -> classSym.compilationUnitInfo.associatedFile)
    }
  }

  /** Get the identifier associated with the given [[sym]], creating a new one if needed. */
  def fetch(sym: Symbol, mode: FetchingMode)(using Context): SymbolIdentifier = mode match {
    case Plain =>
      s2s.getOrElseUpdate(sym, {
        maybeRegisterTastyUnit(sym)
        val overrides = sym.allOverriddenSymbols.toSeq
        val top = overrides.lastOption.getOrElse(sym)
        if (top eq sym) {
          SymbolIdentifier(ast.Symbol(symFullName(sym)))
        } else {
          SymbolIdentifier(fetch(top, Plain).symbol)
        }
      })
    case FieldAccessor =>
      s2sAccessor.getOrElseUpdate(sym, {
        maybeRegisterTastyUnit(sym)
        val overrides = sym.allOverriddenSymbols.toSeq
        val top = overrides.lastOption.getOrElse(sym)
        if (top eq sym) {
          SymbolIdentifier(ast.Symbol(symFullName(sym)))
        } else {
          val recMode =
            if (top.isField) FieldAccessor
            else Plain
          SymbolIdentifier(fetch(top, recMode).symbol)
        }
      })
    case EnumType =>
      s2sEnumType.getOrElseUpdate(sym, {
        maybeRegisterTastyUnit(sym)
        assert(sym.allOverriddenSymbols.isEmpty)
        SymbolIdentifier(ast.Symbol(symFullName(sym)))
      })
  }

  /** Mapping for outer references of member classes: class symbol -> identifier. */
  private val outerFields = MutableMap[Symbol, SymbolIdentifier]()
  private val outerAccessors = MutableMap[Symbol, SymbolIdentifier]()
  private val outerAccessorSymbols = MutableMap[Symbol, stainless.ast.Symbol]()

  private val identityFields = MutableMap[Symbol, SymbolIdentifier]()
  private val identityAccessors = MutableMap[Symbol, SymbolIdentifier]()
  private lazy val identityAccessorSymbol = stainless.ast.Symbol("stainless.lang.identity")

  /** Get the identifier of the ghost field holding the identity of instances of [[cls]]. */
  def fetchIdentityField(cls: Symbol)(using Context): SymbolIdentifier =
    identityFields.getOrElseUpdate(cls, SymbolIdentifier(ast.Symbol(symFullName(cls) + ".$identity")))

  /** Get the identifier of the accessor of the identity of instances of [[cls]].
    *
    * Identity accessors all override each other (a class may inherit them from unrelated traits),
    * so they share the same symbol.
    */
  def fetchIdentityAccessor(cls: Symbol)(using Context): SymbolIdentifier =
    identityAccessors.getOrElseUpdate(cls, SymbolIdentifier(identityAccessorSymbol))

  /** Get the identifier of the field holding the outer instance of the member class [[cls]]. */
  def fetchOuterField(cls: Symbol)(using Context): SymbolIdentifier =
    outerFields.getOrElseUpdate(cls, SymbolIdentifier(ast.Symbol(symFullName(cls) + ".$outer")))

  /** Get the identifier of the accessor of the outer instance of the member class [[cls]].
    *
    * The accessors of all member classes sharing the same topmost member class ancestor [[root]]
    * override each other, so they share the symbol of the accessor of [[root]].
    */
  def fetchOuterAccessor(cls: Symbol, root: Symbol)(using Context): SymbolIdentifier =
    outerAccessors.getOrElseUpdate(cls, {
      val symbol = outerAccessorSymbols.getOrElseUpdate(root, ast.Symbol(symFullName(root) + ".outer"))
      SymbolIdentifier(symbol)
    })

  /** Whether [[id]] identifies the accessor of the outer instance of a member class. */
  def isOuterAccessor(id: stainless.Identifier): Boolean = id match {
    case sid: SymbolIdentifier => outerAccessorSymbols.valuesIterator.contains(sid.symbol)
    case _ => false
  }

  /** Get the identifier for the class invariant of [[sym]]. */
  def fetchInvIdForClass(sym: Symbol)(implicit ctx: Context): SymbolIdentifier = {
    val id = fetch(sym, Plain)
    invs.getOrElse(id, {
      val res = SymbolIdentifier(invSymbol)
      invs(id) = res
      res
    })
  }

}

object SymbolMapping {

  enum FetchingMode {
    case Plain
    case FieldAccessor
    case EnumType
  }

  private def symFullName(sym: Symbol)(using Context): String =
    if (sym `is` TypeParam) {
      sym.showName
    } else {
      sym.fullName.toString.trim.split("\\.")
        .filter(_ != "package$")
        .map(name => if (name.endsWith("$")) name.init else name)
        .map { name =>
          // Strip the _$ introduced for each scope of inner function
          var nme = name
          while (nme.startsWith("_$")) {
            nme = nme.drop(2)
          }
          nme
        }
        .mkString(".")
    }
}
