import stainless.lang._

object StructuralMeasureRebuild {
  sealed abstract class L
  case class C(h: BigInt, t: L) extends L
  case class N() extends L

  // The argument is rebuilt from the fields of `l`, and is as large as `l`
  def rebuild(l: L): BigInt = {
    decreases(l)
    l match {
      case C(_, t) => rebuild(C(1, t))
      case N() => BigInt(0)
    }
  }
}
