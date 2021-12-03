/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

// In order to evaluate tasks, we'll need a Scheduler
import monix.execution.Scheduler.Implicits.global

// A Future type that is also Cancelable
import monix.execution.CancelableFuture

// Task is in monix.eval
import monix.eval.Task

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification.{smartHide, smartHideAll, smartSuccHide}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.core.{Formula, _}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, stop}
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools.atomicFormulas
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, ExpressionTraversal, FormulaTools, PosInExpr, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.TokenStream
import edu.cmu.cs.ls.keymaerax.parser._
import edu.cmu.cs.ls.keymaerax.parser.{AMP, LBRACE, RBRACE}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ext.CounterExampleTool

import scala.annotation.tailrec
import scala.collection.immutable.Nil
import scala.collection.mutable.ListBuffer
import scala.collection.parallel.immutable
import scala.collection.immutable.IndexedSeq
import scala.concurrent.duration.{Duration, DurationInt}
import scala.concurrent.{Await, ExecutionContext, Future, TimeoutException}
import scala.util.{Failure, Success, Try}

/**
  * Tactics for minimizing sequents.
  *
  * @author Ben Gafford
  */
object MinimizationLibrary {
  //region Tactics

  /* Only apply this tactic to Provables that have been unfolded and reduced */
  /* TODO: track source of introduced facts */
  @Tactic(names = "MinQE",
    premises = "*",
    //     smartHideAll -------------------------
    conclusion = "Γ |- Δ",
    displayLevel = "browse")
  lazy val minQE: BuiltInTactic = anon((p: ProvableSig) => {
    val proved = proveBy(p, QEshort)
    assert(proved.isProved, s"minQE requires a Provable that can be proved (within 5 seconds) by QE")
    assert(p.subgoals.length == 1, s"minQE requires Provables with one subgoal; found ${p.subgoals.length} subgoals")
    val simplified = proveBy(p, unfoldProgramNormalizeProofless & smartHideAll)

    val weakenings = getQEWeakenings(simplified.subgoals.head)

    // Right now, trying all possible weakenings. Really should do this more efficiently.
    val provableWeakenings = weakenings.map {
      seq => proveBy(seq, QEshort)
    }.filter {
      x => x.isProved
    }

    val minSequent = if(provableWeakenings.length > 0) {
      provableWeakenings.foldLeft(provableWeakenings.head)((x,y) => if (entails(x.proved, y.proved)) x else y).proved
    } else throw new TacticAssertionError("There should be a provable weakening (id)")

    println("MinSequent: ", minSequent)
    proved.apply(minSequent)
  })

  def getAssumptionWeakenings(original: Sequent): List[Sequent] = {

    // Get all possible sets of sequents
    val candidates = (0 to original.ante.length) flatMap original.ante.combinations

    // Convert candidates (indexed sequence of antecedent formulas) to Sequents
    val sequents = candidates.map {
      case x => Sequent(x, original.succ)
    }
    sequents.toList
  }

  def getQEWeakenings(original: Sequent): List[Sequent] = {
    val weakenings = getAssumptionWeakenings(original)
    weakenings
  }
/*
  def getDomainConstraintWeakenings(original: Sequent): List[Sequent] = {
    val antes = original.ante
    val succs = original.succ

    Sequent(scala.collection.immutable.IndexedSeq[Formula](),
      scala.collection.immutable.IndexedSeq[Formula](KeYmaeraXParser.parse(dropDomainConstraints(KeYmaeraXLexer(succs.toString))).toString().asFormula)) :: Nil
  }
*/
  /* TODO add more */
  def getAutoWeakenings(original: Sequent): List[Sequent] = {
    getAssumptionWeakenings(original)++getDomainConstraintWeakenings(original)
  }

  def getDomainConstraintWeakenings(original: Sequent): List[Sequent] = {

    val fmls = ListBuffer[Formula]()

    original.succ.foreach { fml =>
      val formAug = FormulaAugmentor(fml)
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = e match {
          case Test(q) if q != True => fmls.appendAll(formulaSimplifications(q).map(simp => formAug.replaceAt(p, Test(simp)))); Left(None);
          case ODESystem(ogODE, q) if q != True => fmls.appendAll(formulaSimplifications(q).map(simp => formAug.replaceAt(p, ODESystem(ogODE, simp)))); Left(None);
          case c => Left(None)
        }
        // NOTE TODO negation over everything might mess things up?
        // kind of need things of the form `preconditions -> [ctrl;plant]postconditions`
        override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
          case Imply(pre, Box(prog, f)) => fmls.appendAll(formulaSimplifications(pre).map(simp => formAug.replaceAt(p, Imply(simp, Box(prog,f))))); Left(None);
          case c => Left(None)
        }
      }, fml)
    }
    println("DCWs: " + fmls)
    fmls.map(formula => Sequent(original.ante, scala.collection.immutable.IndexedSeq(formula))).toList
  }

  def formulaSimplifications(f: Formula): List[Formula] = {
    getAssumptionWeakenings(Sequent(IndexedSeq(f), IndexedSeq()))
      .map{ seq => anteToFormula(seq) }
  }

  def getProgramConstraints(fml: Formula) = {
    val constraints = ListBuffer[Formula]()

    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = e match {
          case Test(q) if q != True => constraints.append(q); Left(None);
          case ODESystem(_, q) if q != True => constraints.append(q); Left(None);
          case c => Left(None)
        }
      }, fml)
    constraints
  }

  /** Strip the modality parts of the formula, keep the postconditions. */
  def stripModalities(fml: Formula): Formula = {
    var faug = FormulaAugmentor(fml)
     ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
          case Box(_, f) => faug = FormulaAugmentor(stripModalities(faug.replaceAt(p, f))); Left(Some(stop));
          case Diamond(_, f) => faug = FormulaAugmentor(stripModalities(faug.replaceAt(p, f))); Left(Some(stop));
          case c => Left(None)
        }
      }, fml)
    faug.fml
  }

  /** What we _really_ want is `entails` (as defined below), but auto is not powerful enough to prove many of the
    * weakenings (which we know to be sound). This function will determine which sequent has been weakened (by our mutations)
    * more than the others. Used internally to detect which is Sequent is the minSequent which we want to keep.  */
  /** Note: This doesn't work in general, but is correct under our mutations */
  def isWeaker(s1: Sequent, s2: Sequent): Boolean = {
    assert(s1.succ.length == 1 && s2.succ.length == 1, s"We have not reasoned about Sequents with multiple succedents yet.")
    if(!proveBy(s1, master()).isProved || !proveBy(s2, master()).isProved) {
    throw new IllegalArgumentException("Args must be provable through auto.")
    }

    val ante1 = if(s1.ante.isEmpty) scala.collection.immutable.IndexedSeq[Formula](True) else s1.ante
    val ante2 = if(s2.ante.isEmpty) scala.collection.immutable.IndexedSeq[Formula](True) else s2.ante

    // (1) Do the constraints of the program in s2.succ |- the constraints of the program in s1.succ?
    // (2) Does the non-modality part of s1.succ |- the non-modality part of the succedent in s2.succ
    val weakerSucc = vacuousOrProvable(Sequent(getProgramConstraints(s2.succ.head).toIndexedSeq,
      getProgramConstraints(s1.succ.head).toIndexedSeq)) && vacuousOrProvable(Sequent(IndexedSeq(stripModalities(s1.succ.head)),
        IndexedSeq(stripModalities(s2.succ.head))))
    val weakerAnte = (s1.ante.isEmpty && s2.ante.isEmpty) ||
      (vacuousOrProvable(Sequent(getProgramConstraints(ante1.head).toIndexedSeq,
      getProgramConstraints(ante2.head).toIndexedSeq)) &&
      vacuousOrProvable(Sequent(IndexedSeq(ante1.head),
        IndexedSeq(ante2.head))))

    /*
    // Collect constraints from s1
    {s2.ante++s2.succ}.foreach { fml =>
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = e match {
          case Test(q) if q != True => fmls2.append(q); Left(None);
          case ODESystem(_, q) if q != True => fmls2.append(q); Left(None);
          case c => Left(None)
        }
        override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
          case Imply(pre, Box(prog,f)) => fmls2.append(pre); Left(None);
          case c => Left(None)
        }
      }, fml)
    }

    val fmls1_atomic = fmls1.map(x => atomicFormulas(x)).flatten
    val fmls2_atomic = fmls2.map(x => atomicFormulas(x)).flatten

    println("fmls1: " + fmls1_atomic)
    println("is smaller than: " + fmls2_atomic + "?" + (fmls1_atomic.length <= fmls2_atomic.length))

    fmls1_atomic.length <= fmls2_atomic.length
    */
    weakerSucc && weakerAnte
  }

  def vacuousOrProvable(s: Sequent): Boolean = {
    s.ante.isEmpty ||
      s.succ.head == False ||
      (s.ante.head == True)  ||
    proveBy(s, master()).isProved
  }

  /* Note: This one would be nice, but auto cannot (currently) easily prove these things (e.g.,
  * [{x'=1&x>2}]x>=0 ==> [{x'=1&x>2&y>2}]x>=0
  * */
  def entails(s1: Sequent, s2: Sequent): Boolean = {
    //prove LHS1 |- LHS2, RHS1 |- RHS2
    proveBy(Sequent(s1.ante, s2.ante),master()).isProved &&
      proveBy(Sequent(s1.succ, s2.succ),master()).isProved
  }

def anteToFormula(s: Sequent): Formula = {

  if (s.ante.isEmpty) {
    "true".asFormula
  } else {
    s.ante.foldRight("") {
      (_.toString + "&" + _.toString)
    }.init.asFormula
  }
}
  /*
  def arithmeticWeakenings(f: Formula): List[Formula] = {
    f match {
      case (f: And, false) if f.isPredicateFreeFOL => None
      case (f: Imply, true) if f.isPredicateFreeFOL => None
      case (_: Or, true) => None
      case (_: Equiv, _) => None
      case _ => sequentStepIndex(isAnte)(expr)
    }
  }
*/

  //implicit val ec = ExecutionContext.global

  //def timeoutFuture[A](f: Future[A]): Try[A] =
  //  Try { Await.result(f, 5.seconds) }

  /*
  def tryProofByAuto(p: ProvableSig): ProvableSig = {
    val f = Future { proveBy(p, master()) }
    try {
      timeoutFuture(f) match {
        case Failure(exception) => p
        case Success(proved) => proved
      }
    } catch {
      case e => p
    }
  }
*/
  import scala.concurrent.TimeoutException

  /* TODO: track source of introduced facts */
  @Tactic(names = "MinAuto",
    premises = "*",
    //     smartHideAll -------------------------
    conclusion = "Γ |- Δ",
    displayLevel = "browse")
  lazy val minAuto: BuiltInTactic = anon((p: ProvableSig) => {
    val proved = proveBy(p, master())
    //val proved2 = tryProofByAuto(p).timeout(3.seconds)

    if(!proved.isProved) throw new TacticAssertionError(s"minAuto requires a Provable that can be proved using Auto (within 5 second time budget")

    val simplified = p//proveBy(p, unfoldProgramNormalizeProofless)

    val weakenings = simplified.subgoals.map(x => getAutoWeakenings(x))

    // Right now, trying all possible weakenings. Really should do this more efficiently.
    val provableWeakenings = weakenings.flatten.map {
      case seq => proveBy(seq, master())
    }.filter {
      case prov => prov.isProved
    }

    println("PWS: " + provableWeakenings)

    val minSequent = if(provableWeakenings.length > 0) {
      provableWeakenings.foldLeft(provableWeakenings.head)((x,y) => if (entails(x.proved, y.proved)) x else y)
    }.proved
    else throw new TacticAssertionError("There should be a provable weakening (id)")

    println("MinSequent: ", minSequent)

    //throw new TacticAssertionError("Minimum sequent: )
    proveBy(simplified, master()).apply(minSequent)
  })
}



