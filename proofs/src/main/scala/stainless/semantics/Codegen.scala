/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package semantics

import java.nio.file.{Files, Path}

import inox.semantics.{LeanBackend, Spec}

/** Generates the embeddings of `proofs/semantics.md` with Inox's generators: the Scala evaluator
  * that the tests run, and the Lean definitions that the proofs are stated against.
  * `sbt stainless-proofs/run`. */
object Codegen {
  val source = "semantics.md"
  val scalaOutput = "src/test/scala/stainless/semantics/generated/Semantics.scala"
  val scalaPackage = "stainless.semantics.generated"
  val leanOutput = "lean/Stainless/Semantics.lean"
  val leanNamespace = "Stainless.Semantics"

  /** The measures of the functions that Stainless's semantics adds, with Inox's. Pattern matching
    * recurses on the cases and patterns of a `MatchExpr`, with the fuel of its `eval`. Filling an
    * array counts up to its size. */
  val measures: Map[String, String] = LeanBackend.measures ++ Seq(
    "eval-cases" -> ("sizeOf cases", 0), "match-pattern" -> ("sizeOf p", 0), "match-patterns" -> ("sizeOf ps", 0),
    "match-any" -> ("sizeOf ps", 0), "eval-entries" -> ("sizeOf es", 0),
    "eval-array" -> ("sizeOf e", 1), "eval-index" -> ("sizeOf e", 1)
  ).map { case (f, (size, rank)) => f -> s"termination_by (fuel.toNat, $size, $rank)" } ++ Map(
    "array-fill" -> "termination_by (n - i).toNat\ndecreasing_by omega")

  def scala: String = inox.semantics.Codegen.scala(Path.of(source), scalaPackage)

  /** Lean shows the termination of `eval` and its helpers, which are many more with Stainless's
    * expressions than with Inox's alone, within more than its default number of heartbeats. */
  val heartbeats = 1000000

  def lean: String = LeanBackend(Spec.load(Path.of(source)), source, leanNamespace, measures, LeanBackend.assumed)
    .replaceFirst(s"(?m)^namespace $leanNamespace$$", s"set_option maxHeartbeats $heartbeats\n\nnamespace $leanNamespace")

  def main(args: Array[String]): Unit = {
    for ((out, text) <- Seq(scalaOutput -> scala, leanOutput -> lean)) {
      val p = Path.of(out)
      Files.createDirectories(p.getParent)
      Files.writeString(p, text)
      println(s"Wrote $p")
    }
  }
}
