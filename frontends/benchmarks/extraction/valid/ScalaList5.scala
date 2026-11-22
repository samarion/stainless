// The Scala list is extracted as its model, stainless.stdlib.List

object ScalaList5 {
  type MyList[T] = List[T]
  def foobar[T](l: MyList[T]) = {
    require(l.size > 0)
    l.head
  }
}
