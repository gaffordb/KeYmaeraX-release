/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.IsabelleSyntax.listConj
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.core.{Formula, _}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, stop}
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools.atomicFormulas
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import monix.eval.Task
import monix.execution.Scheduler.Implicits.global

import scala.::
import scala.collection.immutable.{IndexedSeq, Nil}
import scala.collection.mutable.ListBuffer
import scala.concurrent.duration.{Duration, DurationInt}
import scala.concurrent.{Await, TimeoutException}
import scala.util.{Failure, Success}

/**
  * Tactics for minimizing sequents.
  *
  * @author Ben Gafford, Myra Dotzel
  */
object MinimizationLibrary {
  //region Tactics

  type Weakening = (Formula, PosInExpr)

  /* TODO: track source of introduced facts */
  @Tactic(names = "MinQE",
    premises = "*",
    //     smartHideAll -------------------------
    conclusion = "Γ |- Δ",
    displayLevel = "browse")
  lazy val minQE: BuiltInTactic = anon((p: ProvableSig) => {
    val timeout = 60.seconds
    val proved = tryProofByQE(p.conclusion, timeout)
    assert(proved.isProved, s"minQE requires a Provable that can be proved (within" + timeout + ") by QE")
    assert(p.subgoals.length == 1, s"minQE requires Provables with one subgoal; found ${p.subgoals.length} subgoals")
    val simplified = proveBy(p, unfoldProgramNormalizeProofless)

    val weakenings = getQEWeakenings(simplified.subgoals.head)

    // Right now, trying all possible weakenings. Really should do this more efficiently.
    val provableWeakenings = weakenings.map {
      seq => tryProofByQE(seq, timeout)
    }.filter {
      x => x.isProved
    }

    val minSequent = if(provableWeakenings.nonEmpty) {
      provableWeakenings.foldLeft(provableWeakenings.head)((x,y) => if (isWeaker(x.proved, y.proved)) x else y).proved
    } else throw new TacticAssertionError("There should be a provable weakening (id). Initial: " + proved +"\nGot " + weakenings)

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
          case _ => Left(None)
        }
        // kind of need things of the form `preconditions -> [ctrl;plant]postconditions`
        override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
          case Imply(pre, Box(prog, f)) => {
            fmls.appendAll(formulaSimplifications(pre).map(simp => formAug.replaceAt(p, Imply(simp, Box(prog, f)))))
          }; Left(None);
          case _ => Left(None)
        }
      }, fml)
    }
    //fmls.foreach { x => println("DCW: " + x) }
    fmls.map(formula => Sequent(original.ante, scala.collection.immutable.IndexedSeq(formula))).toList
  }

  /** Get the powerset of the conjuncts from fml */
  def formulaSimplifications(f: Formula): List[Formula] = {
    val atomic_conjuncts = (conjuncts(f) filter { x =>
      !x.toString.contains("&")
    })
    (((0 to atomic_conjuncts.length) flatMap atomic_conjuncts.combinations) map listConj).toList
  }

  /* Note: This only works if the relevant conjuncts occur before any instances of programs */
  def conjuncts(fml: Formula): List[Formula] = {
    val out = ListBuffer[Formula]()
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
        case Box(_,_) => Nil; Left(Some(stop))
        case Diamond(_,_) => Nil; Left(Some(stop))
        case And(l, rest) => out.appendAll(List(l,rest)); Left(None);
        case Imply(l, Box(_,_)) => out.append(l); Left(None);
        case c => Left(None)
      }
    }, fml)
    out.toList
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
    constraints.toList
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

  def bundleFormulas(fmls: List[Formula]): IndexedSeq[Formula] = IndexedSeq(listConj(fmls))

  /** What we _really_ want is `entails` (as defined below), but auto is not powerful enough to prove many of the
    * weakenings (which we know to be sound). This function will determine which sequent has been weakened (by our mutations)
    * more than the others. Used internally to detect which is Sequent is the minSequent which we want to keep.  */
  /** Note: This doesn't work in general, but is correct under our mutations */
  def isWeaker(s1: Sequent, s2: Sequent): Boolean = {
    assert(s1.succ.length == 1 && s2.succ.length == 1, s"We have not reasoned about Sequents with multiple succedents yet.")
    /*
    if(!proveBy(s1, master()).isProved || !proveBy(s2, master()).isProved) {
    throw new IllegalArgumentException("Args must be provable through auto.")
    }
*/
    val ante1 = if(s1.ante.isEmpty) scala.collection.immutable.IndexedSeq[Formula](True) else s1.ante
    val ante2 = if(s2.ante.isEmpty) scala.collection.immutable.IndexedSeq[Formula](True) else s2.ante


    // (1) Do the constraints of the program in s2.succ |- the constraints of the program in s1.succ?
    // (2) Does the non-modality part of s1.succ |- the non-modality part of the succedent in s2.succ
    val weakerSucc = vacuousOrProvable(Sequent(bundleFormulas(getProgramConstraints(s2.succ.head)),
      bundleFormulas(getProgramConstraints(s1.succ.head)))) && vacuousOrProvable(Sequent(IndexedSeq(stripModalities(s1.succ.head)),
        IndexedSeq(stripModalities(s2.succ.head))))
    val weakerAnte = (s1.ante.isEmpty && s2.ante.isEmpty) ||
      (vacuousOrProvable(Sequent(bundleFormulas(getProgramConstraints(bundleFormulas(s1.ante.toList).head)),
        bundleFormulas(getProgramConstraints(bundleFormulas(s2.ante.toList).head)))) &&
      vacuousOrProvable(Sequent(IndexedSeq(stripModalities(bundleFormulas(ante2.toList).head)),
        IndexedSeq(stripModalities(bundleFormulas(ante1.toList).head)))))

    weakerSucc && weakerAnte
  }

  /** This one is less true in general but way cheaper to compute.
    * All of our mutations strictly remove tokens, so this is a fine proxy for which one has been weakened the most.
    * Therefore, to detect which of two mutations is more weakened, we can simply count tokens. */
  def isWeakerByTokenCount(s1: Sequent, s2: Sequent): Boolean = {
    assert(s1.succ.length == 1 && s2.succ.length == 1, s"We have not reasoned about Sequents with multiple succedents yet.")

    val s1Tokens = (s1.succ flatMap {x => (atomicFormulas(x) ++ getProgramConstraints(x)).filter(fml => fml != True)}) ++
      (s1.ante flatMap {x => (atomicFormulas(x) ++ getProgramConstraints(x)).filter(fml => fml != True)})

    val s2Tokens = (s2.succ flatMap {x => (atomicFormulas(x) ++ getProgramConstraints(x)).filter(fml => fml != True)}) ++
      (s2.ante flatMap {x => (atomicFormulas(x) ++ getProgramConstraints(x)).filter(fml => fml != True)})

    s1Tokens.length <= s2Tokens.length
  }

  /** Weakenings get weird when you get to empty sequents,
    * which happens a lot when you remove the last element from an assumption.
    * When reasoning about weakenings, it makes sense that we consider empty sequents or '==>True' / 'False==>' are "Provable"
    * to be weaker than everything. */
  def vacuousOrProvable(s: Sequent): Boolean = {
    s.ante.isEmpty ||
      s.succ.head == False ||
      (s.ante.head == True)  ||
    proveBy(s, master()).isProved
  }

  /** Convert the ante of a sequent to a single conjuncted formula
    * e.g., a1, a2, a3 |- Delta  goesto a1 & a2 & a3 |- Delta
    */
def anteToFormula(s: Sequent): Formula = {
  if (s.ante.isEmpty) {
    "true".asFormula
  } else {
    s.ante.foldRight("") {
      (_.toString + "&" + _.toString)
    }.init.asFormula
  }
}

  def tryProofByAuto(s: Sequent, t: Duration): Option[ProvableSig] = {
    val tryProof = Task(proveBy(s, master())).runAsync

    try {
      Await.result(tryProof, t)
    } catch {
      case _: TimeoutException => println("Auto timed out after " + t.toString)
      case e => println("Trying proof, caught: " + e.toString)
    }

    tryProof.value match {
      case Some(Success(value)) => Some(value);
      case Some(Failure(ex)) => println(s"ERROR: ${ex.getMessage}"); None;
      case _ => None
    }
  }

  def tryProofByQE(s: Sequent, t: Duration): ProvableSig = {
    val tryProof = Task(proveBy(s, master())).runAsync

    try {
      Await.result(tryProof, t) // Blocking
    } catch {
      case e: TimeoutException => println("Auto timed out after " + t.toString)
    }

    val proved = tryProof.value match {
      case Some(Success(value)) => Some(value);
      case Some(Failure(ex)) => println(s"ERROR: ${ex.getMessage}"); None;
      case _ => None
    }
    proved match {
      case Some(prov) => prov //isProved will be true
      case _ => ProvableSig.startProof(s) //isProved will be false
    }
  }

  def getProvableWeakenings(s: Sequent): List[Sequent] = {
    val weakenings = getAutoWeakenings(s).toSet
    //println("weakenings: ", weakenings)

    // Right now, trying all possible weakenings. Really should do this more efficiently.
    weakenings.map {
      seq =>
        tryProofByAuto(seq, 10.seconds) match {
          case Some(prov) => prov
          case _ => ProvableSig.startProof("false".asFormula) // just an arbitrary thing where p.proved is false
        }
    }.filter { prov =>
      prov.isProved
    }.map(x => x.proved).toList
  }

  /** Greedily get weakenings from your weakest weakening until you can no longer weaken anything provable.
    * This is a lazy way of exploring these sequents, but it expensive and is not optimal.
    * */
  def refineWeakenings(weakenings: List[Sequent], witnessed: List[Sequent] = Nil): List[Sequent] = {
    weakenings match {
      case Nil => witnessed
      case x :: xs =>
        val candidateWeakenings = getProvableWeakenings(x).filter(fml => !witnessed.contains(fml)) // we only care about weakenings that we haven't seen before
        if(candidateWeakenings.isEmpty) {
          refineWeakenings(xs, witnessed)// x has no more weakenings
        } else {
          val candidateWeakening = if(candidateWeakenings.length == 1) candidateWeakenings.head else candidateWeakenings.foldLeft(candidateWeakenings.head)((x,y) => if (isWeakerByTokenCount(x, y)) x else y)
          refineWeakenings(List(candidateWeakening), candidateWeakenings++witnessed) ++ refineWeakenings(xs, candidateWeakenings++witnessed)
        }
    }
  }

  /* TODO: track source of introduced facts */
  @Tactic(names = "MinAuto",
    premises = "*",
    //     smartHideAll -------------------------
    conclusion = "Γ |- Δ",
    displayLevel = "browse")
  lazy val minAuto: BuiltInTactic = anon((p: ProvableSig) => {
    val proved = tryProofByAuto(p.conclusion, 10.seconds)

    if(proved.isEmpty || !proved.head.isProved) {
      throw new TacticAssertionError(s"minAuto requires a Provable that can be proved using Auto (within 10 second time budget")
    }

    val simplified = p

    //assert(simplified.subgoals.length == 1, "we don't want to try to minimize over multiple goals, too hard")

    val provableWeakenings = simplified.subgoals flatMap (x=> getProvableWeakenings(x))

    //println("PWS: " + provableWeakenings)

    val minSequent = if(provableWeakenings.nonEmpty) {
      provableWeakenings.foldLeft(provableWeakenings.head)((x,y) => if (isWeakerByTokenCount(x, y)) x else y)
    }
    else throw new TacticAssertionError("There should be a provable weakening (id)")

    println("MinSequent: ", minSequent)

    // Uncomment for hack to pass info to frontend, but can't see unused facts:
    //throw new TacticAssertionError("Minimum sequent: " + minSequent)
    proveBy(simplified, master()).apply(minSequent)
  })

  /* TODO: track source of introduced facts */
  @Tactic(names = "MinAutoXtreme",
    premises = "*",
    //     smartHideAll -------------------------
    conclusion = "Γ |- Δ",
    displayLevel = "browse")
  lazy val minAutoXtreme: BuiltInTactic = anon((p: ProvableSig) => {
    val proved = tryProofByAuto(p.conclusion, 10.seconds)

    if(proved.isEmpty || !proved.head.isProved) {
      throw new TacticAssertionError(s"minAuto requires a Provable that can be proved using Auto (within 5 second time budget")
    }

    val simplified = p

    //assert(simplified.subgoals.length == 1, "we don't want to try to minimize over multiple goals, too hard")

    val provableWeakenings = simplified.subgoals flatMap (x=> refineWeakenings(x::Nil))

    //println("PWS: " + provableWeakenings)

    val minSequent = if(provableWeakenings.nonEmpty) {
      provableWeakenings.foldLeft(provableWeakenings.head)((x,y) => if (isWeakerByTokenCount(x, y)) x else y)
    }
    else throw new TacticAssertionError("There should be a provable weakening (id)")

    println("MinSequent: ", minSequent)

    // Uncomment for hack to pass info to frontend, but can't see unused facts:
    //throw new TacticAssertionError("Minimum sequent: " + minSequent)
    proveBy(simplified, master()).apply(minSequent)
  })

  /** Facts are all formulas in the antecedent, all those in the succedent, minus the modal formulas,
    * plus the constraints over the programs */
  def getFactsFromSequent(s: Sequent): List[Formula] = {
    //val simplified = proveBy(s, unfoldProgramNormalizeProofless)
    s.ante.map { x=> atomicFormulas(x).toSet } ++ s.succ.map { x=> atomicFormulas(x).toSet }

    val tokens = (s.succ flatMap {x => atomicFormulas(x) ++ getProgramConstraints(x) }) ++
      (s.ante flatMap {x => (atomicFormulas(x) ++ getProgramConstraints(x)).filter(fml => fml != True)})

    tokens.toSet.toList
  }
}



