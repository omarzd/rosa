/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Definitions._
import purescala.Trees._
import purescala.Common._
import purescala.TypeTrees._

import real.TreeOps._
import real.{FixedPointFormat => FPFormat}
import real.Trees._

class CodeGenerator(reporter: Reporter, ctx: LeonContext, options: RealOptions, prog: Program) {

  def specToCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], precision: Precision): Program = precision match {
    case FPPrecision(bts) => specToFixedCode(programId, objectId, vcs, precision)
    case _ => specToFloatCode(programId, objectId, vcs, precision)
  }


  private def getNonRealType(precision: Precision): TypeTree = (precision: @unchecked) match {
    case Float64 => Float64Type
    case Float32 => Float32Type
    case DoubleDouble => FloatDDType
    case QuadDouble => FloatQDType
  }



  private def specToFloatCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], precision: Precision): Program = {
    var defs: Seq[Definition] = Seq.empty
    val invariants: Seq[Expr] = Seq.empty

    for (vc <- vcs) {
      val f = vc.funDef
      val id = f.id
      val floatType = getNonRealType(precision)
      val returnType = floatType // FIXME: check that this is actually RealType
      val args: Seq[VarDecl] = f.args.map(decl => VarDecl(decl.id, floatType))

      val funDef = new FunDef(id, returnType, args)
      funDef.body = f.body

      funDef.precondition = f.precondition

      vc.spec(precision) match {
        case Some(spec) => funDef.postcondition = Some(specToExpr(spec))
        case _ =>
      }

      defs = defs :+ funDef
    }

    val newProgram = Program(programId, ObjectDef(objectId, defs, invariants))
    newProgram
  }


  private def specToFixedCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], precision: Precision): Program = {
    var defs: Seq[Definition] = Seq.empty
    val invariants: Seq[Expr] = Seq.empty

    val solver = new RealSolver(ctx, prog, options.z3Timeout)

    for (vc <- vcs) {
      val f = vc.funDef
      val id = f.id
      val args: Seq[VarDecl] = f.args.map(decl => VarDecl(decl.id, Int32Type))
      val funDef = new FunDef(id, Int32Type, args)
      
      // convert to SSA form, then run through FloatApproximator
      println("original: " + vc.body)
      val ssaBody = idealToActual(toSSA(vc.body), vc.variables)
      println("\n ssaBody: " + ssaBody)

      println("variables: " + vc.variables)

      val transformer = new FloatApproximator(reporter, solver, precision, vc.pre, vc.variables)
      val (newBody, newSpec) = transformer.transformWithSpec(ssaBody)
      println("newBody: " + newBody)
      println("newSpec: " + newSpec)
      println("\n variables: " + transformer.variables)

      funDef.body = f.body

      defs = defs :+ funDef
    }

    val newProgram = Program(programId, ObjectDef(objectId, defs, invariants))
    newProgram
  }

  // Accepts SSA format only
  def translateToFP(expr: Expr, formats: Map[Expr, FPFormat], bitlength: Int): Expr = expr match {
    case And(exprs) =>
      And(exprs.map(e => translateToFP(e, formats, bitlength)))

    /*    +    */
    case EqualsF(vr, PlusF(lhs, rhs)) =>
      val resultFormat = formats(vr)
      val mx = resultFormat.f
      val (ll, rr, mr) = alignOperators(lhs, rhs, formats, bitlength)
      val assignment =
        if (mx == mr) Plus(ll, rr)
        else if (mx <= mr) RightShift(Plus(ll, rr), (mr - mx))
        else LeftShift(Plus(ll, rr), (mx - mr))  // Fixme: really?
      Equals(vr, assignment)

    /*    -    */
    case EqualsF(vr, MinusF(lhs, rhs)) =>
      val resultFormat = formats(vr)
      val mx = resultFormat.f
      val (ll, rr, mr) = alignOperators(lhs, rhs, formats, bitlength)
      val assignment = 
        if (mx == mr) Minus(ll, rr)
        else if (mx <= mr) RightShift(Minus(ll, rr), (mr - mx))
        else LeftShift(Minus(ll, rr), (mx - mr))  // Fixme: really?
      Equals(vr, assignment)

    /*    *    */
    case EqualsF(vr, TimesF(lhs, rhs)) =>
      val resultFormat = formats(vr)
      val mx = resultFormat.f
      val (mult, mr) = multiplyOperators(lhs, rhs, formats, bitlength)
      val assignment = 
        if (mx == mr) mult
        else if (mr - mx >= 0) RightShift(mult, (mr - mx))
        else LeftShift(mult, mx - mr)
      Equals(vr, assignment)

    /*    /    */
    case EqualsF(vr, DivisionF(lhs, rhs)) =>
      val resultFormat = formats(vr)
      val mx = resultFormat.f
      Equals(vr, divideOperators(lhs, rhs, mx, formats, bitlength))

    /*    unary_-    */
    case EqualsF(vr, rhs) => Equals(vr, translateToFP(rhs, formats, bitlength))

    case v @ Variable(id) => v // FIXME: shouldn't this be the ideal buddy?
    case FloatLiteral(r, exact) =>
      val bits = FPFormat.getFormat(r, bitlength).f
      LongLiteral(rationalToLong(r, bits))
    case UMinusF( t ) => UMinus(translateToFP(t, formats, bitlength))  
  }

  
  private def alignOperators(x: Expr, y: Expr, formats: Map[Expr, FPFormat], bitlength: Int): (Expr, Expr, Int) = (x, y) match {
    case (v1 @ Variable(_), v2 @ Variable(_)) =>
      val my = formats(v1).f
      val mz = formats(v2).f

      if (mz == my) (v1, v2, my)
      else if (my <= mz) (LeftShift(v1, (mz - my)), v2, mz)
      else (v1, LeftShift(v2, (my - mz)), my)

    case (v @ Variable(_), FloatLiteral(r, exact)) =>
      val my = formats(v).f
      val mz = FPFormat.getFormat(r, bitlength).f
      val longValue = rationalToLong(r, mz)
      if (my == mz) (v, LongLiteral(longValue), mz)
      else if (my <= mz) (LeftShift(v, (mz - my)), LongLiteral(longValue), mz)
      else (v, LeftShift(LongLiteral(longValue), (my - mz)), my)

    case (FloatLiteral(r, exact), v @ Variable(_)) =>
      val mz = formats(v).f
      val my = FPFormat.getFormat(r, bitlength).f
      val longValue = rationalToLong(r, my)
      if (my == mz) (LongLiteral(longValue), v, mz)
      else if (my <= mz) (LeftShift(LongLiteral(longValue), (mz - my)), v, mz)
      else (LongLiteral(longValue), LeftShift(v, (my - mz)), my)

    case (FloatLiteral(r1, exact1), FloatLiteral(r2, exact2)) =>
      val my = FPFormat.getFormat(r1, bitlength).f
      val mz = FPFormat.getFormat(r2, bitlength).f
      val i1 = rationalToLong(r1, my)
      val i2 = rationalToLong(r2, mz)
      if (my == mz) (LongLiteral(i1), LongLiteral(i2), mz)
      else if (my <= mz) (LeftShift(LongLiteral(i1), (mz - my)), LongLiteral(i2), mz)
      else (LongLiteral(i1), LeftShift(LongLiteral(i2), (my - mz)), my)
  }

  def multiplyOperators(x: Expr, y: Expr, formats: Map[Expr, FixedPointFormat], bitlength: Int): (Times, Int) = (x, y) match {
     case (v1 @ Variable(_), v2 @ Variable(_)) =>
      val my = formats(v1).f
      val mz = formats(v2).f
      (Times(v1, v2), my + mz)

    case (v @ Variable(_), FloatLiteral(r, exact)) =>
      val my = formats(v).f
      val mz = FPFormat.getFormat(r, bitlength).f
      val i = rationalToLong(r, mz)
      (Times(v, LongLiteral(i)), my + mz)

    case (FloatLiteral(r, exact), v @ Variable(_)) =>
      val my = FPFormat.getFormat(r, bitlength).f
      val i = rationalToLong(r, my)
      val mz = formats(v).f
      (Times(LongLiteral(i), v), my + mz)

    case (FloatLiteral(r1, exact1), FloatLiteral(r2, exact2)) =>
      val my = FPFormat.getFormat(r1, bitlength).f
      val i1 = rationalToLong(r1, my)
      val mz = FPFormat.getFormat(r2, bitlength).f
      val i2 = rationalToLong(r2, mz)
      (Times(LongLiteral(i1), LongLiteral(i2)), my + mz)
   }

   def divideOperators(x: Expr, y: Expr, mx: Int, formats: Map[Expr, FixedPointFormat], bitlength: Int): Division = (x, y) match {
     case (v1 @ Variable(_), v2 @ Variable(_)) =>
      val my = formats(v1).f
      val mz = formats(v2).f
      val shift = mx + mz - my
      Division(LeftShift(v1, shift), v2)

    case (v @ Variable(_), FloatLiteral(r, exact)) =>
      val my = formats(v).f
      val mz = FPFormat.getFormat(r, bitlength).f
      val i = rationalToLong(r, mz)
      val shift = mx + mz - my
      Division(LeftShift(v, shift), LongLiteral(i))

    case (FloatLiteral(r, exact), v @ Variable(_)) =>
      val my = FPFormat.getFormat(r, bitlength).f
      val i = rationalToLong(r, my)
      val mz = formats(v).f
      val shift = mx + mz - my
      Division(LeftShift(LongLiteral(i), shift), v)

    case (FloatLiteral(r1, exact1), FloatLiteral(r2, exact2)) =>
      val my = FPFormat.getFormat(r1, bitlength).f
      val i1 = rationalToLong(r1, my)
      val mz = FPFormat.getFormat(r2, bitlength).f
      val i2 = rationalToLong(r2, mz)
      val shift = mx + mz - my
      Division(LeftShift(LongLiteral(i1), shift), LongLiteral(i2))
   }


  private def rationalToLong(r: Rational, f: Int): Long = {
    return (r * Rational(math.pow(2, f))).roundToInt.toLong
  }

}