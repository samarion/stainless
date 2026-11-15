import stainless.lang._

object ObjectClassInvariants2 {

  sealed abstract class S[A]
  case class G[A](height: BigInt) extends S[(A, A)] {
    require(height > 0)
  }

  def g[A](h: BigInt): S[(A, A)] = G[A](h) // The invariant doesn't hold
}
