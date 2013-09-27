import leon.Real
import Real._

object Grading {

  //def isRatio(x:Real): Boolean = {0.0 <= x && x <= 1.0}

  def invariant(project: Real, homeworks: Real, quiz: Real) : Boolean = {
    //require(isRatio(project) && isRatio(homeworks) && isRatio(quiz))
    require(0.0 < project && project < 1.0 && 0.0 < homeworks && homeworks < 1.0 && 0.0 < quiz && quiz < 1.0)

    goodGradingNoRounding(project, homeworks, quiz) >= badGradingNoRounding(project, homeworks, quiz)

  } holds

  def goodGradingNoRounding(project: Real, homeworks: Real, quiz: Real) : Real = {
    //require(isRatio(project) && isRatio(homeworks) && isRatio(quiz))
    require(0.0 < project && project < 1.0 && 0.0 < homeworks && homeworks < 1.0 && 0.0 < quiz && quiz < 1.0)

    val result: Real = 
      if (project >= 0.5 && (0.45*homeworks + 0.55*quiz) >= 0.5) {
        ((5*(0.55*project + 0.45*(0.45*homeworks + 0.55*quiz)) + 1.24999)*2.0)/2.0

      } else {   
        val grade = ((5*(0.55*project + 0.45*(0.45*homeworks + 0.55*quiz)) + 1.24999)*2.0)/2.0
        if (grade < 3.5) { //min(grade, 3.5)
          grade
        } else {
          3.5
        }
      }
    result
  } ensuring (result => 1.0 <= result && result <= 6.0)


  def badGradingNoRounding(project: Real, homeworks: Real, quiz: Real) : Real = {
    //require(isRatio(project) && isRatio(homeworks) && isRatio(quiz))
    require(0.0 < project && project < 1.0 && 0.0 < homeworks && homeworks < 1.0 && 0.0 < quiz && quiz < 1.0)

    val result: Real =  
      if (project >= 0.6 && quiz >= 0.6 && homeworks >= 0.6)
        ((5*(0.55*project + 0.2*homeworks + 0.25*quiz) + 1.24999)*2.0)/2.0
      else {
        val grade = ((5*(0.55*project + 0.2*homeworks + 0.25*quiz) + 1.24999)*2.0)/2.0
        if (grade < 3.5) {
          grade
        } else {
          3.5
        }
      }
    result
  } ensuring (result => 1.0 <= result && result <= 6.0)
}

/*object GoodPolicy {
  val version = "December 2012, Version 1.0"

  def roundToHalf(grade: Double) : Double =
    round(grade*2.0)/2.0

  def ratioToGrade(ratio: Double) : Double =
    roundToHalf(5*ratio + 1.24999)

  def baseGrade(project: Double, theory: Double) =
    ratioToGrade(0.55*project + 0.45*theory)

  val threshold = 0.5

  def isRatio(x:Double):Boolean = {0.0 <= x && x <= 1.0}

  // Input: ratios of points achieved relative to maximum possible
  def finalGrade(project: Double, homeworks: Double, quiz: Double) : Double = {
    require(isRatio(project) && isRatio(homeworks) && isRatio(quiz))
    val theory = 0.45*homeworks + 0.55*quiz
    val base = baseGrade(project, theory)
    if (project >= threshold && theory >= threshold)
      base
    else
      min(base, 3.5)
  } ensuring (result => 1.0 <= result && result <= 6.0)
}


object BadPolicy {
  val version = "December 2012, Version 0.0"

  def roundToHalf(grade: Double) : Double =
    round(grade*2.0)/2.0

  def ratioToGrade(ratio: Double) : Double =
    roundToHalf(5*ratio + 1.24999)

  val threshold = 0.6

  def isRatio(x:Double):Boolean = {0.0 <= x && x <= 1.0}

  def finalGrade(project: Double, homeworks: Double, quiz: Double) : Double = {
    require(isRatio(project) && isRatio(homeworks) && isRatio(quiz))
    val base = ratioToGrade(0.55*project + 0.2*homeworks + 0.25*quiz)
    if (project >= threshold && quiz >= threshold && homeworks >= threshold)
      base
    else
      min(base, 3.5)
  } ensuring (result => 1.0 <= result && result <= 6.0)
}*/

