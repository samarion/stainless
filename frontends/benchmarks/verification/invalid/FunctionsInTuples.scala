// Counterexamples with functions in constructor fields, which Princess models
// only give as individuals of an uninterpreted sort (epfl-lara/inox#390)
object FunctionsInTuples {
  def test(t: (BigInt => BigInt, BigInt => BigInt)): Unit = {
    assert(t._1(0) == t._2(0))
  }
}
