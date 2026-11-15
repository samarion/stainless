import stainless.lang._
import stainless.annotation._
import scala.collection.immutable.{Vector => ScalaVector}

object i1401b {
  // No, must annotate the field with @extern
  case class Vec[T](s: ScalaVector[T])
}