/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.tags.CheckinTest
import org.scalatest.{FlatSpec, Matchers, PrivateMethodTester}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._


/**
  * @author Nathan Fulton
  */
@CheckinTest
class UnicodeParserTests extends FlatSpec with Matchers with PrivateMethodTester {
  "The parser" should "parse conjunctions of inequalities and such" in {
    "g > 0 ∧ 1 ≥ c ∧ c ≥ 0".asFormula shouldBe "g > 0 & 1>=c & c>=0".asFormula
  }

  it should "parse disjunctions of inequalities with implications and equivalences" in {
    "1=1 ∨ 2=2 → 3=3 ∨ 2=2 ↔ 3=3 ∨ 2=2 ← 3=3 ∨ ∀ eps (∃ delta (eps < delta))".asFormula shouldBe
      "1=1 | 2=2 -> 3=3 | 2=2 <-> 3=3 | 2=2 <- 3=3 | \\forall eps (\\exists delta (eps < delta))".asFormula
  }

  it should "parse choice" in {
    "[x:=2; ∪ x:=3;]x>=1".asFormula shouldBe "[x:=2; ++ x:=3;]x>=1".asFormula
    "[x:=2; ∩ x:=3;]x>=1".asFormula shouldBe "[{x:=2;^@ ++ x:=3;^@}^@]x>=1".asFormula
  }

  it should "parse repetition" in {
    "[{x:=x+1;}×]x>=1".asFormula shouldBe "[{{x:=x+1;^@}*}^@]x>=1".asFormula
  }

  it should "parse unequal" in {
    "1 ≠ 2".asFormula shouldBe "1 != 2".asFormula
  }

  "Tactic parser" should "parse when unicode is used as a tactic argument" in {
    """cut("g > 0 ∧ 1 ≥ c ∧ c ≥ 0")""".asTactic shouldBe """cut("g>0 & 1>=c & c>=0")""".asTactic
  }
}
