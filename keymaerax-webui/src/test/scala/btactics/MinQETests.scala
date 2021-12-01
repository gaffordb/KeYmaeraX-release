package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.OnAll
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification.{smartHide, smartHideAll, smartSuccHide}
import edu.cmu.cs.ls.keymaerax.btactics.MinimizationLibrary.{minQE}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger._
import edu.cmu.cs.ls.keymaerax.core.{Box, Formula, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest
import edu.cmu.cs.ls.keymaerax.infrastruct.DependencyAnalysis._

/**
  * Tests for the simple QE logger
  * Only logs first order formulae
  */
class MinQETests extends TacticTestBase {
  "QE Hider: 2 ante, 1 succ, 1 valid ante" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = "x<0, x < -1, y<z, y>0, g>0 \n  ==> x<1, z>0, v>0".asSequent

    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minQE)
    println("Proved: " + pr.proved)
    println("MinSeq: " + pr.minSequent)
  }

  "QE Hider: 2 ante, 2 succ, 1 necessary ante, both dependent" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = "x>0, x=2 \n  ==> x>=2, y=-1".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq,minQE)
    println("After" + pr.prettyString)
    println("Minseq: " + pr.minSequent.prettyString)
  }

  "QE Hider: QE for id" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = "x>0 & y>0 \n  ==> x>0".asSequent
    println("Before" + seq.prettyString)

    val pr = proveBy(seq,minQE)
    println("After" + pr.prettyString)
    println("MinSeq: " + pr.minSequent)
  }

}
