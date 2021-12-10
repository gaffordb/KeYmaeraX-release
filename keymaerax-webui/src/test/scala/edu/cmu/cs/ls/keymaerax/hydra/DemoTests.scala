package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.MinimizationLibrary.{minAuto, minQE}
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.LoneElement._

import scala.collection.immutable.IndexedSeq

/**
  * Tests the proof tree data structure and minAuto
  */
class DemoTests extends TacticTestBase {
  "bad model" should "show lots of unusable facts" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent =
        """
ArchiveEntry "badACC"

Definitions
      Real A;   /* The controlled car accelerates with acceleration A */
      Real B;   /* The controlled car brakes with acceleration -B */
      Real vL;  /* Constant velocity of the lead car */
    End.

    ProgramVariables
      Real pL;  /* Position of the lead car */
      Real pC;  /* Position of the controlled car */
      Real vC;  /* Velocity of the controlled car */
      Real aC;  /* Acceleration of the controlled car */
    End.

Problem
      /* Initial conditions */
      ( A > 0 & B > 0 & vL >0 & pC < pL &
      (vC>=vL -> (pL-pC > vC*(vL-vC)/-B + 1/2*-B*((vL-vC)/-B)^2 - (vL * ((vL-vC)/-B)))))
      ->
      [
        {
          /* Control */
          {
            /* Safely assign acceleration or braking for the controlled car */
             {?(vC>=vL -> (pL-pC > vC*(vC-vL)/-B + 1/2*-B*((vC-vL)/-B)^2 - (vL * ((vC-vL)/-B)))); aC := A;}
             {?vC=0;aC := 0;}
             ++{aC := -B;}
          }
          /* Continuous dynamics and event triggers */
          {
            { pL' = vL, pC' = vC, vC' = aC &
              (vC>=vL -> (pL-pC <= vC*(vC-vL)/-B + 1/2*-B*((vC-vL)/-B)^2 - (vL * ((vC-vL)/-B)))) & vC >= 0 }
            ++
            { pL' = vL, pC' = vC, vC' = aC &
              (vC>=vL -> (pL-pC <= vC*(vC-vL)/-B + 1/2*-B*((vC-vL)/-B)^2 - (vL * ((vC-vL)/-B)))) & vC >= 0 }
          }
        }*
      ]
      /* Safety condition */
      ( pC <= pL )
End.

Tactic "automated"
minAuto
End.
End.""".stripMargin
      val proofId = db.createProof(modelContent)

      val tactic = ArchiveParser(modelContent).loneElement.tactics.loneElement._3

      var tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals.loneElement.runTactic("guest",
        LazySequentialInterpreter(_, throwWithDebugInfo = false), tactic, "proof", wait = true)
      tree = DbProofTree(db.db, proofId.toString)
      val p = tree.root.provable

      println("All witnessed facts: " + tree.root.allWitnessedFacts)
      println("All used facts: " + tree.root.allUsedFacts)
      println("All unused facts: " + tree.root.allUnusedFacts)
      tree.root.allUnusedFacts.length shouldBe 0
    }
  }

  }