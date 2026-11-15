/** Enumerating a Scala set is not supported, as the order of its elements is not a function of the set. */
object ScalaSetNoModel {
  def elements(s: Set[Int]): List[Int] = s.toList
}
