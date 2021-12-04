package btactics

import edu.cmu.cs.ls.keymaerax.btactics.MinimizationLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.master
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

import scala.collection.immutable.IndexedSeq
import scala.concurrent.duration.DurationInt

/**
  * Tests for the simple QE logger
  * Only logs first order formulae
  */
class MinAutoTests extends TacticTestBase {
  "Compound implication RHS" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = "==> x>0 & y>0 -> x>0".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minAuto)
    println("After" + pr.prettyString)
    println("MinSeq: " + pr.minSequent)
  }

  /*
  "Bug with smartHideAll" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    println("TODO BUG. works without smarthideall.")
    val seq = " \n ==> x>0 -> [{x'=5 & x>2}]x>0".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, unfoldProgramNormalizeProofless & smartHideAll & minAuto)
    println("After" + pr.prettyString)
    println("MinSeq: " + pr.minSequent)
  }
*/
  "Domain constraints RHS" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = " \n ==> x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0-> [{x'=1&x>2&y>2}]x>=0".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minAuto)
    println("After" + pr.prettyString)
    println("MinSeq: " + pr.minSequent)

    println(proveBy("x=H(), v=0, g()>0 ==> [{x'=v,v'=-g()}][?x=0;v:=-c()*v;++?x>=0;](x>=0&x<=H())".asSequent, master()))
  }

  "Bouncyball minAuto" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0 -> [{x'=v,v'=-g()}{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minAuto)
    println("After: " + pr.prettyString)
    println("MinSeq: " + pr.minSequent)
    pr.minSequent shouldBe "==> x=H()&v=0&g()>0&true->[{x'=v,v'=-g()}{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent

    val seq2 = "  ==>  x>=0&x=H()&v=0&g()>0 ->[{x'=v,v'=-g() & x<=H()}{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    println("Before" + seq2.prettyString)
    val pr2 = proveBy(seq2, minAuto)
    println("After" + pr2.prettyString)
    println("MinSeq: " + pr2.minSequent)
    pr2.minSequent shouldBe "==>  true->[{x'=v,v'=-g()&x<=H()}{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent

    val seq3 = "  ==>  x=H()&v=0&g()>0->[{x'=v,v'=-g()}{?x=0;?x<=H;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    println("Before" + seq3.prettyString)
    val pr3 = proveBy(seq3, minAuto)
    println("After" + pr3.prettyString)
    println("MinSeq: " + pr3.minSequent)
    pr3.minSequent shouldBe "==>  x=H()&v=0&g()>0->[{x'=v,v'=-g()}{?x=0;?true;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent

    val seq4 = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;?x<=H&false;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    println("Before" + seq4.prettyString)
    val pr4 = proveBy(seq4, minAuto)
    println("After" + pr4.prettyString)
    println("minSeq: " + pr4.minSequent)

    pr4.minSequent shouldBe "==> x=H()&v=0&g()>0&true->[{x'=v,v'=-g()}{?x=0;?x<=H&false;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
  }

  /*
  "Bouncyball XTREME" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    //FYI this takes forever (10 min or so)
    val seq = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0 -> [{x'=v,v'=-g()}{?x=0;v:=-c()*v;?x>=0;}](x>=0&x<=H())".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minAutoXtreme)
    println("After: " + pr.prettyString)
    println("MinSeq: " + pr.minSequent)
    //pr.minSequent shouldBe "x=H(), v=0, g()>0 ==> [{x'=v,v'=-g()}][?x=0;v:=-c()*v;++?x>=0;](x>=0&x<=H())".asSequent

    val seq2 = "  ==>  x>=0&x=H()&v=0&g()>0 ->[{x'=v,v'=-g() & x<=H()}{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    println("Before" + seq2.prettyString)
    val pr2 = proveBy(seq2, minAutoXtreme)
    println("After" + pr2.prettyString)
    println("MinSeq: " + pr2.minSequent)
    //pr2.minSequent shouldBe "==> [{x'=v,v'=-g() & x<=H()}][{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent

    val seq3 = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;?x<=H;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    println("Before" + seq3.prettyString)
    val pr3 = proveBy(seq3, minAutoXtreme)
    println("After" + pr3.prettyString)
    println("MinSeq: " + pr3.minSequent)
    //pr3.minSequent shouldBe seq

    val seq4 = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;?x<=H&false;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    println("Before" + seq4.prettyString)
    val pr4 = proveBy(seq4, minAutoXtreme)
    println("After" + pr4.prettyString)
    println("MinSeq: " + pr4.minSequent)
  }
*/
  "ODE contstraints deep" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = "  ==> [x:=1; ++ y:=*; ?y>5; {x'=1&x>2&y>2}]x>=0".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minAuto)
    println("After" + pr.prettyString)
    println("MinSeq: " + pr.minSequent)
  }


  "Subformulas" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val s1 = " ==> [{x'=1&x>2&y>2}]x>=0".asSequent
    val s2 = " ==> [{x'=1&x>2}]x>=0".asSequent

    val s3 = "==> y<1 & x<2".asSequent
    val s4 = "==> y<1".asSequent

    val w1 = isWeaker(s1, s2)

    isWeaker(s1, s2) shouldBe false
    isWeaker(s3, s4) shouldBe true
    isWeaker(s2, s1) shouldBe true
    isWeaker(s4, s3) shouldBe false
  }

  "Test is weaker with random formulas" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val formula_generator = new RandomFormula()

    val fml = formula_generator.nextFormula(1)

    /* */
    1 to 10 foreach { _ =>
      val seq = Sequent(IndexedSeq(), IndexedSeq(formula_generator.nextFormula(3)))
        println("seq: " + seq)
        assert(isWeaker(seq, seq))
    }
  }
  "Test QE weakenings manual" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>

    val s1 = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    val s2 = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;?x<=H;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    val s3 = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;?y<=H;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    val s4 = "x=H(), v=0, g()>0 ==>  [{x'=v,v'=-g()}][?x=0;v:=-c()*v;++?x>=0;](x>=0&x<=H())".asSequent
    val s5 = "x>=0,x=H(),v=0,g()>0,1>=c(),c()>=0 ==>  [{x'=v,v'=-g()}][?x=0;v:=-c()*v;++?x>=0;](x>=0&x<=H())".asSequent

    isWeaker(s1, s2) shouldBe true
    isWeaker(s1,s3) shouldBe true
    isWeaker(s2,s3) shouldBe false
    isWeaker(s3,s2) shouldBe false
    isWeaker(s4,s5) shouldBe true
    isWeaker(s5,s4) shouldBe false
  }

  "Test QE TC weakenings manual" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>

    val s1 = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    val s2 = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;?x<=H;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    val s3 = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;?y<=H;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    val s4 = "x=H(), v=0, g()>0 ==>  [{x'=v,v'=-g()}][?x=0;v:=-c()*v;++?x>=0;](x>=0&x<=H())".asSequent
    val s5 = "x>=0,x=H(),v=0,g()>0,1>=c(),c()>=0 ==>  [{x'=v,v'=-g()}][?x=0;v:=-c()*v;++?x>=0;](x>=0&x<=H())".asSequent

    isWeakerByTokenCount(s1, s2) shouldBe true
    isWeakerByTokenCount(s1,s3) shouldBe true
    isWeakerByTokenCount(s4,s5) shouldBe true
    isWeakerByTokenCount(s5,s4) shouldBe false
  }

  "Test QE weakenings simple" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>

    val s1 = " x<0 & y<0 | z<0 ==>  t<0 & h<0 | b<0".asSequent
    val s2 = " x<0 & y<0 ==>  t<0 & h<0 | b<0".asSequent
    isWeaker(s1, s2) shouldBe true
    isWeaker(s2, s1) shouldBe false

    val s3 = " x<0 & y<0 | z<0 ==>  t<0 & h<0".asSequent
    isWeaker(s1, s3) shouldBe false
    isWeaker(s2, s3) shouldBe false
    isWeaker(s3, s1) shouldBe true
    isWeaker(s3, s1) shouldBe true

    val s4 = " x<0 & y<0 -> z<0 ==>  t<0 & h<0 -> b<0".asSequent
    val s5 = " x<0 & y<0 ==>  t<0 & h<0 -> b<0".asSequent
  }

  "Test QE weakenings automatic" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val formula_generator = new RandomFormula(1)

    1 to 1000 foreach { _ =>
      // nextSequent kinda gives junk values, so build sequents manually instead
      // val seq = formula_generator.nextSequent(3)

      val seq = Sequent(IndexedSeq(formula_generator.nextFormula(5)), IndexedSeq(formula_generator.nextFormula(5)))
      println("Random Sequent: ", seq)
      val validSucc = seq.succ.headOption match {
        case Some(x) => {
          x
        }
        case _ => "x=1".asFormula
      }
      val validSeq = Sequent(seq.ante, IndexedSeq(validSucc))
      println("Valid Sequent: " + validSeq)
      getQEWeakenings(Sequent(validSeq.ante, validSeq.succ)) foreach { seqSimp =>
          println("Simplification: " + seqSimp)
          try {
            assert(isWeaker(seqSimp, validSeq))
          }
          catch {
            case e: IllegalArgumentException => if(!(e.toString.contains("Args must be provable through auto."))) {print("e: " + e.toString); throw e}
          }
        }
      }
  }

  "Strip modalities" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val s1 = "x=0 & [{x'=1&x>2&y>2}]x>=0".asFormula
    val s2 = "[{x'=1&x>2}]x>=0".asFormula
    val s3 = "y<1 & x<2".asFormula
    val s4 = "y<1".asFormula

    println(stripModalities(s1))
    println(stripModalities(s2))
    println(stripModalities(s3))
    println(stripModalities(s4))
  }

  "Test formula simplifications" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val s1 = "x=0 & [{x'=1&x>2&y>2}]x>=0".asFormula
    val s2 = "x<1 & y=1 | y=2".asFormula
    val s3 = "y<1 & x<2".asFormula
    val s4 = "y<1".asFormula
    val s5 = "(y=0 & x=0 | x<1) -> [{x'=1&x>2&y>2}]x>=0".asFormula
    val s6 = "x=0 & [{x'=1&x>2&y>2}]x>=0".asFormula

    println(stripModalities(s1))
    println(stripModalities(s2))
    println(stripModalities(s3))
    println(stripModalities(s4))
    println(formulaSimplifications(s5))
  }


  "Test getFactsFromSequent" should "test the function" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val s1 = "x=0 & [{x'=1&x>2&y>2}]x>=0".asFormula
    val s2 = "x<1 & y=1 | y=2".asFormula
    val s3 = "y<1 & x<2".asFormula
    val s4 = "y<1".asFormula
    val s5 = "(y=0 & x=0 | x<1) -> [{x'=1&x>2&y>2}]x>=0".asFormula
    val s6 = "x=0 & [{x'=1&x>2&y>2}]x>=0".asFormula

    println(stripModalities(s1))
    println(stripModalities(s2))
    println(stripModalities(s3))
    println(stripModalities(s4))
    println(formulaSimplifications(s5))

    //val pr = proveBy(seq, minAuto)
    //println("After" + pr.prettyString)
    //println("MinSeq: " + pr.minSequent)
  }

  "Constraint weakenings" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val fml = "==>x>1 & y>1 & z>1 -> [x:=1; ++ y:=*; ?y>5; {x'=1&x>2&y>2}]x>=0".asSequent

    val fml2 = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    println(getDomainConstraintWeakenings(fml))
    println(getDomainConstraintWeakenings(fml2))

    println(proveBy(fml, minAuto))
    println(proveBy(fml2, minAuto))
  }

  "Refine weakenings" should "output used arguments (takes a couple minutes)" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val fml = "==>x>1 & y>1 & z>1 -> [?false & true & x<1 & x>1;]x>=0".asSequent
    println(refineWeakenings(fml::Nil))
    proveBy(fml, minAutoXtreme).minSequent shouldBe "==> true->[?false;]x>=0".asSequent
  }
}
