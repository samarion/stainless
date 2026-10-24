object FunctionFieldEquality {
  case class Box(f: BigInt => BigInt)

  def same(a: Box, b: Box): Boolean = a == b
}
