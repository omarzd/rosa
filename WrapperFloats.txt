
import ceres.common.{DoubleDouble, QuadDouble}

object WrappedFloats {


  // For compiling the generated code
  implicit def float2wrapped(d: Float): WrappedFloat = WrappedFloat(d)
  case class WrappedFloat(x: Float) {
    def +/-(y: Float): Boolean = true
    def unary_!() = x
  }

  implicit def double2wrapped(d: Double): WrappedDouble = WrappedDouble(d)
  case class WrappedDouble(x: Double) {
    def +/-(y: Double): Boolean = true
    def unary_!() = x
  }

  implicit def ddouble2wrapped(d: DoubleDouble): WrappedDDouble = WrappedDDouble(d)
  case class WrappedDDouble(x: DoubleDouble) {
    def +/-(y: DoubleDouble): Boolean = true
    def unary_!() = x
  }

  implicit def qdouble2wrapped(d: QuadDouble): WrappedQDouble = WrappedQDouble(d)
  case class WrappedQDouble(x: QuadDouble) {
    def +/-(y: QuadDouble): Boolean = true
    def unary_!() = x
  }
}