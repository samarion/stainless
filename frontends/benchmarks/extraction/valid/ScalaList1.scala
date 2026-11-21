// The Scala list is extracted as its model, stainless.covcollection.List

object ScalaList1 {
  def foobar[T](l: List[T]) = {
    require(l.size > 0)
    l.head
  }
}
