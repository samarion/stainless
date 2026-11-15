/** The Scala `Set` and `Map` are the built-in sets and maps of Stainless. */
object ScalaMapSet {
  def add(s: Set[BigInt], x: BigInt): Set[BigInt] = {
    s + x
  }.ensuring(res => res.contains(x) && s.subsetOf(res))

  def remove(s: Set[BigInt], x: BigInt): Set[BigInt] = {
    s - x
  }.ensuring(res => !res.contains(x) && res.subsetOf(s))

  def symmetricDifference(a: Set[BigInt], b: Set[BigInt]): Set[BigInt] = {
    (a ++ b) -- (a & b)
  }.ensuring(res => res.subsetOf(a ++ b))

  def literals: Boolean = {
    val s: Set[BigInt] = Set(BigInt(1), BigInt(2))
    s.contains(1) && !s.contains(3) && Set.empty[BigInt].isEmpty && Set[BigInt]().isEmpty && s.nonEmpty
  }.ensuring(res => res)

  def positives(s: Set[BigInt]): Set[BigInt] = s.filter(_ > 0)

  def successors(s: Set[BigInt]): Set[BigInt] = s.map(_ + 1)

  def neighbours(s: Set[BigInt]): Set[BigInt] = s.flatMap(x => Set(x - 1, x + 1))

  def comprehension(s: Set[BigInt]): Set[BigInt] = for (x <- s if x > 0) yield x + 1

  def quantifiers(s: Set[BigInt]): Boolean = s.forall(_ > 0) || s.exists(_ <= 0)

  def put[K, V](m: Map[K, V], k: K, v: V): Map[K, V] = {
    m.updated(k, v)
  }.ensuring(res => res.contains(k) && res(k) == v && res.get(k) == Some(v))

  def delete[K, V](m: Map[K, V], k: K): Map[K, V] = {
    m - k
  }.ensuring(res => !res.contains(k) && res.get(k) == None)

  def lookup(m: Map[BigInt, BigInt], k: BigInt): BigInt = {
    m.get(k) match {
      case Some(v) => v
      case None => BigInt(0)
    }
  }.ensuring(_ == m.getOrElse(k, BigInt(0)))

  def defined(m: Map[BigInt, BigInt], k: BigInt): Option[BigInt] = {
    m.get(k)
  }.ensuring(res => res.isDefined == m.contains(k))

  def mapLiterals: Boolean = {
    val m: Map[BigInt, BigInt] = Map(BigInt(1) -> BigInt(2))
    val e: Map[BigInt, BigInt] = Map.empty
    m(1) == 2 && !m.contains(2) && !e.contains(1) && (e + (BigInt(1) -> BigInt(2))) == m
  }.ensuring(res => res)

  case class Env(vars: Map[String, BigInt], seen: Set[String]) {
    def bind(x: String, v: BigInt): Env = {
      Env(vars + (x -> v), seen + x)
    }.ensuring(res => res.vars(x) == v && res.seen.contains(x))
  }
}
