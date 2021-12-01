package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.MinimizationLibrary.{minAuto, minQE}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.btactics.{BelleLabels, Idioms, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core.{Formula, Sequent}
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, SuccPosition}
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import org.scalatest.LoneElement._
import testHelper.KeYmaeraXTestTags.TodoTest

import scala.collection.immutable.{IndexedSeq, List}

/**
  * Tests the proof tree data structure.
  * Created by smitsch on 3/31/17.
  */
class WitnessedFactsTests extends TacticTestBase {

  "Empty tree" should "have a single goal" in withTactics {
    withDatabase { db =>
      val modelContent = "ProgramVariables Real x; End. Problem x>0 -> x>0 End."
      val proofId = db.createProof(modelContent)
      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals.loneElement.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula)))
      tree.root.children shouldBe empty
      tree.root.goal shouldBe tree.openGoals.head.goal
      tree.locate("()").get.goal shouldBe tree.root.goal
      tree.tactic shouldBe nil
    }
  }

  "Tactic execution" should "create a tree with one open goal from implyR" in withDatabase { db =>
    val modelContent = "ProgramVariables Real x; End. Problem x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait = true)

    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 2
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("implyR") :: Nil
    tree.openGoals.loneElement.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    tree.root.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.localProvable.subgoals should have size 1
    tree.root.localProvable.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children.head.localProvable.subgoals should have size 1
    tree.root.children.head.localProvable.subgoals.head shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.makerShortName shouldBe Some("implyR")
    tree.locate("(1,0)").get.goal shouldBe tree.root.children.head.goal

    tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.provable.subgoals.loneElement shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))

    tree.tactic shouldBe implyR('R, "x>0 -> x>0".asFormula)
  }

  it should "create a proved tree from QE" in withDatabase { db =>
    withMathematica { _ =>
      val ante = "y>0 & x>0"
      val modelContent = "ProgramVariables Real x; Real y; End. Problem y>0 & x>0 -> x>0 End."
      val proofId = db.createProof(modelContent)

      var tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals should have size 1
      tree.openGoals.loneElement.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait = true)
      tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), minQE, "minQE", wait = true)

      tree = DbProofTree(db.db, proofId.toString)


      println("uhhhh minSequent?" + tree.root.provable.minSequent)
      println("uhhhh witnessedFacts?" + tree.root.allWitnessedFacts)

      tree.openGoals shouldBe empty
      tree.root.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("y>0 & x>0 -> x>0".asFormula))
      tree.root.localProvable.subgoals should have size 1
      tree.root.localProvable.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq("y>0 & x>0 -> x>0".asFormula))
      tree.root.children should have size 1
      tree.root.children.head.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("y>0 & x>0 -> x>0".asFormula))
      tree.root.children.head.localProvable.subgoals shouldBe empty
      tree.root.children.head.makerShortName shouldBe Some("minQE")
      tree.root.children.head shouldBe 'proved
      tree.locate("(1,0)").get.goal shouldBe tree.root.children.head.goal

      tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("y>0 & x>0 -> x>0".asFormula))
      tree.root.provable.subgoals shouldBe empty
      tree.root.provable shouldBe 'proved

      tree shouldBe 'proved

      tree.tactic shouldBe minQE
    }
  }

  it should "create a proved tree from implyR ; minQE" in withDatabase { db => withMathematica { _ =>
    val modelContent = "ProgramVariables Real x; Real y; End. Problem x>0 & y>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait=true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), minQE, "minQE", wait=true)

    val rt = DbProofTree(db.db, proofId.toString)
    rt.nodes should have size 3
    rt.openGoals shouldBe empty
    rt.root.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 & y>0 -> x>0".asFormula))
    rt.root.localProvable.subgoals should have size 1
    rt.root.localProvable.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 & y>0 -> x>0".asFormula))
    rt.root.children should have size 1
    val c1 = rt.root.children.head
    c1.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 & y>0 -> x>0".asFormula))
    c1.goal shouldBe Some(Sequent(IndexedSeq("x>0 & y>0".asFormula), IndexedSeq("x>0".asFormula)))
    c1.localProvable.subgoals should have size 1
    c1.makerShortName shouldBe Some("implyR")
    rt.locate("(1,0)").get.goal shouldBe c1.goal
    c1.children should have size 1
    val c2 = c1.children.head
    c2.localProvable.conclusion shouldBe Sequent(IndexedSeq("x>0 & y>0".asFormula), IndexedSeq("x>0".asFormula))
    c2.goal shouldBe 'empty
    c2.localProvable.subgoals shouldBe empty
    c2.makerShortName shouldBe Some("minQE")
    rt.locate("(2,0)").get.goal shouldBe c2.goal

    rt.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 & y>0 -> x>0".asFormula))
    rt.root.provable.subgoals shouldBe empty
    rt.root.provable shouldBe 'proved

    rt shouldBe 'proved

    println("All witnessed facts: " + tree.root.allWitnessedFacts)
    println("All used facts: " + tree.root.allUsedFacts)
    println("All unused facts: " + tree.root.allUnusedFacts)

    rt.tactic shouldBe implyR('R, "x>0 & y>0 -> x>0".asFormula) & minQE
  }}

  it should "get unused facts" in withDatabase { db => withMathematica { _ =>
    val modelContent = "Definitions      /* function symbols cannot change their value */\n  Real H;        /* initial height */\n  Real g;        /* gravity */\n  Real c;        /* damping coefficient */\nEnd.\n\nProgramVariables /* program variables may change their value over time */\n  Real x, v;     /* height and velocity */\nEnd.\n\nProblem\n  x>=0 & x=H\n  & v=0 & g>0 & 1>=c&c>=0\n ->\n  [\n      {x'=v,v'=-g}\n      {?x=0; v:=-c*v;  ++  ?x>=0;}\n  ] (x>=0 & x<=H)\nEnd."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), minAuto, "minAuto", wait=true)
    tree = DbProofTree(db.db, proofId.toString)
    val rt = DbProofTree(db.db, proofId.toString)

    rt.root.provable shouldBe 'proved

    rt shouldBe 'proved

    println("All witnessed facts: " + tree.root.allWitnessedFacts)
    println("All used facts: " + tree.root.allUsedFacts)
    println("All unused facts: " + tree.root.allUnusedFacts)
  }}
}