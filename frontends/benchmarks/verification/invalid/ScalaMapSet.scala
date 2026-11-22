object ScalaMapSet {
  def undefined(m: Map[BigInt, BigInt], k: BigInt): BigInt = m(k)

  def removed(s: Set[BigInt], x: BigInt): Boolean = {
    (s - x).contains(x)
  }.ensuring(res => res)
}
