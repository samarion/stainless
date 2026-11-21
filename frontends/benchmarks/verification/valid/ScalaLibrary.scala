import stainless.lang.{Option => _, Some => _, None => _, Either => _, Left => _, Right => _, _}

/** The Scala `Option`, `List`, `Seq` and `Either` are verified through their models
  * in `stainless.covcollection`.
  */
object ScalaLibrary {
  case class Entry(key: BigInt, value: Option[BigInt], tags: List[BigInt])

  def get(o: Option[BigInt]): BigInt = o match {
    case Some(x) => x
    case None => BigInt(0)
  }

  def incr(o: Option[BigInt]): Option[BigInt] = {
    o.map(_ + 1)
  }.ensuring(_.isDefined == o.isDefined)

  def orZero(o: Option[BigInt]): BigInt = o.getOrElse(BigInt(0))

  def wrap(x: BigInt): Option[BigInt] = Option(x)

  def both(a: Option[BigInt], b: Option[BigInt]): Option[BigInt] =
    for (x <- a; y <- b) yield x + y

  def sum(xs: List[BigInt]): BigInt = xs match {
    case Nil => BigInt(0)
    case x :: rest => x + sum(rest)
  }

  def sumAppend(xs: List[BigInt], ys: List[BigInt]): Unit = {
    xs match {
      case Nil => ()
      case _ :: rest => sumAppend(rest, ys)
    }
  }.ensuring(_ => sum(xs ++ ys) == sum(xs) + sum(ys))

  def three: List[BigInt] = List(BigInt(1), BigInt(2), BigInt(3))

  def sumThree: Unit = {
    ()
  }.ensuring(_ => sum(three) == 6)

  def headOption(xs: List[BigInt]): Option[BigInt] = xs match {
    case x :: _ => Some(x)
    case Nil => None
  }

  def first(xs: List[BigInt]): BigInt = {
    require(xs.nonEmpty)
    xs.head
  }

  def doubled(xs: List[BigInt]): List[BigInt] = {
    xs.map(_ * 2)
  }.ensuring(_.length == xs.length)

  def positives(xs: List[BigInt]): List[BigInt] = {
    xs.filter(_ > 0)
  }.ensuring(_.forall(_ > 0))

  def total(xs: List[BigInt]): BigInt = xs.foldLeft(BigInt(0))(_ + _)

  def values(es: List[Entry]): List[BigInt] =
    for (e <- es; v <- e.value.toList) yield v

  def firstTag(e: Entry): BigInt = if (e.tags.isEmpty) BigInt(0) else e.tags.head

  def headOr[A](xs: List[A], default: A): A = xs.headOption.getOrElse(default)

  def seq(xs: Seq[BigInt]): Seq[BigInt] = {
    xs.map(_ + 1) :+ BigInt(0)
  }.ensuring(_.nonEmpty)

  def pair: Seq[BigInt] = Seq(BigInt(1), BigInt(2))

  def either(e: Either[BigInt, Boolean]): BigInt = e match {
    case Left(x) => x
    case Right(b) => if (b) BigInt(1) else BigInt(0)
  }

  def rightBiased(e: Either[BigInt, BigInt]): Either[BigInt, BigInt] = {
    e.map(_ + 1)
  }.ensuring(_.isLeft == e.isLeft)

  def someValue(s: Some[BigInt]): BigInt = s.value
}
