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
  // these are in MinAutoTests now
}
