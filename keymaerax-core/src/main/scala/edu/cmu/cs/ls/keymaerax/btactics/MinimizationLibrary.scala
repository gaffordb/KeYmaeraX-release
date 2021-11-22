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
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ext.CounterExampleTool

import scala.annotation.tailrec

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
    val simplified = proveBy(p, prop & smartHideAll)

    val weakenings = getWeakenings(simplified.subgoals.head)
    val provableWeakenings = weakenings.map {
      case seq => proveBy(seq, QE)
    }.filter {
      case prov => prov.isProved
    }

    val minSequent = provableWeakenings.minBy(x => x.proved.ante.length).proved

    proveBy(simplified, QE).apply(minSequent)
  })

  def getWeakenings(original: Sequent): List[Sequent] = {
    // Get all possible sets of sequents
    val candidates = (0 to original.ante.length) flatMap original.ante.combinations

    // Convert candidates (indexed sequence of antecedent formulas) to Sequents
    val sequents = candidates.map {
      case x => Sequent(x, original.succ)
    }
    sequents.toList
  }
}
