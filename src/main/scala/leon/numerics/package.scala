package leon


package object numerics {

  case class UnsupportedFragmentException(msg: String) extends Exception(msg)

  object Sat extends Enumeration {
    type Sat = Value
    // caps so it does not clash with the type name
    val SAT = Value("SAT")
    val UNSAT = Value("UNSAT")
    val Unknown = Value("UNKNOWN")
  }


}
