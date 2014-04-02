package leon
package utils

import scala.annotation.implicitNotFound

@implicitNotFound("No implicit debug section found in scope. You need define an implicit DebugSection to use debug/ifDebug")
sealed abstract class DebugSection(val name: String, val mask: Int)

case object DebugSectionSolver       extends DebugSection("solver",       1 << 0)
case object DebugSectionSynthesis    extends DebugSection("synthesis",    1 << 1)
case object DebugSectionTimers       extends DebugSection("timers",       1 << 2)
case object DebugSectionOptions      extends DebugSection("options",      1 << 3)
case object DebugSectionVerification extends DebugSection("verification", 1 << 4)
case object DebugSectionTermination  extends DebugSection("termination",  1 << 5)
case object DebugSectionTrees        extends DebugSection("trees",        1 << 6)
case object DebugSectionPositions    extends DebugSection("positions",    1 << 7)
case object DebugSectionReals        extends DebugSection("reals",        1 << 8)
case object DebugSectionApprox       extends DebugSection("approx",       1 << 9)
case object DebugSectionRealProver   extends DebugSection("rprover",      1 << 10)

object DebugSections {
  val all = Set[DebugSection](
    DebugSectionSolver,
    DebugSectionSynthesis,
    DebugSectionTimers,
    DebugSectionOptions,
    DebugSectionVerification,
    DebugSectionTermination,
    DebugSectionTrees,
    DebugSectionPositions,
    DebugSectionReals,
    DebugSectionApprox,
    DebugSectionRealProver
  )
}
