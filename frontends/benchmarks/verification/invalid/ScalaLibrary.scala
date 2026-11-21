/** The preconditions of the Scala library are those of its model. */
object ScalaLibrary {
  def first(xs: List[BigInt]): BigInt = xs.head

  def value(o: Option[BigInt]): BigInt = o.get
}
