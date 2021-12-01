/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification.{smartHide, smartHideAll, smartSuccHide}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.core.{Formula, _}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools.atomicFormulas
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, ExpressionTraversal, PosInExpr, Position, SuccPosition}
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
import scala.util.Try

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
      provableWeakenings.foldLeft(provableWeakenings.head)((x,y) => if (isWeaker(x.proved, y.proved)) x else y).proved
    } else throw new TacticAssertionError("There should be a provable weakening (id)")

    println("MinSequent: ", minSequent)
    proveBy(simplified, QE).apply(minSequent)
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

        override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
          case Imply(pre, Box(prog,f)) => fmls.appendAll(formulaSimplifications(pre)); Left(None);
          case c => Left(None)

        }
      }, fml)
    }
    println("DCWs: " + fmls)
    fmls.map(formula => Sequent(original.ante, scala.collection.immutable.IndexedSeq(formula))).toList
  }

  def formulaSimplifications(f: Formula): List[Formula] = {
    proveBy(Sequent(scala.collection.immutable.IndexedSeq(f),scala.collection.immutable.IndexedSeq()), unfoldProgramNormalizeProofless)
      .subgoals.flatMap(x=> getAssumptionWeakenings(x))
      .map{ seq => anteToFormula(seq) }.toList
  }

  /* Note: This doesn't work in general, but is correct under our mutations */
  def isWeaker(s1: Sequent, s2: Sequent): Boolean = {
    val fmls1 = ListBuffer[Formula]()
    val fmls2 = ListBuffer[Formula]()

    // Collect constraints from s1
    {s1.ante++s1.succ}.foreach { fml =>
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = e match {
          case Test(q) if q != True => fmls1.append(q); Left(None);
          case ODESystem(_, q) if q != True => fmls1.append(q); Left(None);
          case c => Left(None)
        }
      }, fml)
    }

    // Collect constraints from s1
    {s2.ante++s2.succ}.foreach { fml =>
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = e match {
          case Test(q) if q != True => fmls2.append(q); Left(None);
          case ODESystem(_, q) if q != True => fmls2.append(q); Left(None);
          case c => Left(None)
        }
      }, fml)
    }

    val fmls1_atomic = fmls1.map(x => atomicFormulas(x))
    val fmls2_atomic = fmls2.map(x => atomicFormulas(x))

    fmls1_atomic.length <= fmls2_atomic.length
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

  /* TODO: track source of introduced facts */
  @Tactic(names = "MinAuto",
    premises = "*",
    //     smartHideAll -------------------------
    conclusion = "Γ |- Δ",
    displayLevel = "browse")
  lazy val minAuto: BuiltInTactic = anon((p: ProvableSig) => {
    val simplified = p//proveBy(p, unfoldProgramNormalizeProofless)

    val weakenings = simplified.subgoals.map(x => getAutoWeakenings(x))

    println("CWS: " + weakenings)
    println("CWS2: " + weakenings.flatten)

    // Right now, trying all possible weakenings. Really should do this more efficiently.
    val provableWeakenings = weakenings.flatten.map {
      case seq => proveBy(seq, master())
    }.filter {
      case prov => prov.isProved
    }

    println("PWS: "+ provableWeakenings)

    val minSequent = if(provableWeakenings.length > 0) {
      provableWeakenings.foldLeft(provableWeakenings.head)((x,y) => if (isWeaker(x.proved, y.proved)) x else y)
    }.proved
    else throw new TacticAssertionError("There should be a provable weakening (id)")
    println("MinSequent: ", minSequent)
    println("ogseq: ", simplified.minSequent)
    proveBy(simplified, master()).apply(minSequent)
  })
}



