object MemberClassesUnsupported {

  trait Generic[T] {
    case class Inner(t: T)
  }

  trait WithObject {
    object Inner
  }

  case object Obj {
    case class InCaseObject()
  }

  def local: BigInt = {
    case class Local() {
      case class InLocal()
    }
    0
  }

}
