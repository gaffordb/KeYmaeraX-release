package btactics

import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification.smartHideAll
import edu.cmu.cs.ls.keymaerax.btactics.MinimizationLibrary.{entails, formulaSimplifications, getQEWeakenings, isWeaker, minAuto, minQE, stripModalities}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{master, unfoldProgramNormalizeProofless}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.{Box, Choice, Expression, Formula, Imply, ODESystem, Program, Sequent, Test, True}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools.atomicFormulas
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.{FormulaAugmentor, ProgramAugmentor}

import scala.collection.immutable.IndexedSeq
import scala.collection.mutable.ListBuffer

/**
  * Tests for the simple QE logger
  * Only logs first order formulae
  */
class MinAutoTests extends TacticTestBase {
  "QE Hider: 2 ante, 1 succ, 1 valid ante" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = "x<0, x < -1, y<z, y>0, g>0 \n  ==> x<1, z>0, v>0".asSequent

    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minAuto)
    println("Proved: " + pr.proved)
    println("MinSeq: " + pr.minSequent)
  }

  "QE Hider: 2 ante, 2 succ, 1 necessary ante, both dependent" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = "x>0, x=2 \n  ==> x>=2, y=-1".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minAuto)
    println("After" + pr.prettyString)
    println("Minseq: " + pr.minSequent.prettyString)
  }

  "QE Hider: QE for id" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = "x>0 & y>0 \n  ==> x>0".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minAuto)
    println("After" + pr.prettyString)
    println("MinSeq: " + pr.minSequent)
  }

  "Compound implication RHS" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = "==> x>0 & y>0 -> x>0".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minAuto)
    println("After" + pr.prettyString)
    println("MinSeq: " + pr.minSequent)
  }

  "Bug with smartHideAll" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    println("TODO BUG. works without smarthideall.")
    val seq = " \n ==> x>0 -> [{x'=5 & x>2}]x>0".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, unfoldProgramNormalizeProofless & smartHideAll & minAuto)
    println("After" + pr.prettyString)
    println("MinSeq: " + pr.minSequent)
  }

  "Domain constraints RHS" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = " \n ==> x>0 -> [{x'=1&x>2&y>2}]x>=0".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minAuto)
    println("After" + pr.prettyString)
    println("MinSeq: " + pr.minSequent)
  }

  "Bouncyball" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq = "  ==>  x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0->[{x'=v,v'=-g()}{?x=0;v:=-c()*v;++?x>=0;}](x>=0&x<=H())".asSequent
    println("Before" + seq.prettyString)
    val pr = proveBy(seq, minAuto)
    println("After" + pr.prettyString)
    println("MinSeq: " + pr.minSequent)
  }

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
    //val seq1Atomic = proveBy(Sequent(scala.collection.immutable.IndexedSeq(), scala.collection.immutable.IndexedSeq(seq1)),
    //  unfoldProgramNormalizeProofless).subgoals
    //val seq2Atomic = atomicFormulas(seq2)

    val w1 = isWeaker(s1, s2)

    isWeaker(s1, s2) shouldBe false
    isWeaker(s3, s4) shouldBe true
    isWeaker(s2, s1) shouldBe true
    isWeaker(s4, s3) shouldBe false

    //val pr = proveBy(seq, minAuto)
    //println("After" + pr.prettyString)
    //println("MinSeq: " + pr.minSequent)
  }

  "Test is weaker with random formulas" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val formula_generator = new RandomFormula()

    val fml = formula_generator.nextFormula(1)

    /* */
    1 to 10 foreach { _ =>
      val seq = Sequent(IndexedSeq(), IndexedSeq(formula_generator.nextFormula(3)))
        //val seq = Sequent(IndexedSeq(), IndexedSeq(fml))
        println("seq: " + seq)
        assert(isWeaker(seq, seq))
    }
  }

  "Test QE weakenings" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
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
      //val seq = Sequent(IndexedSeq(), IndexedSeq(fml))
      //println("seq: " + seq)
      //assert(isWeaker(seq, seq))

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

    //val pr = proveBy(seq, minAuto)
    //println("After" + pr.prettyString)
    //println("MinSeq: " + pr.minSequent)
  }

  "Test formula simplifications" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val s1 = "x=0 & [{x'=1&x>2&y>2}]x>=0".asFormula
    val s2 = "x<1 & y=1 | y=2".asFormula
    val s3 = "y<1 & x<2".asFormula
    val s4 = "y<1".asFormula

    println(stripModalities(s1))
    println(stripModalities(s2))
    println(stripModalities(s3))
    println(stripModalities(s4))

    //val pr = proveBy(seq, minAuto)
    //println("After" + pr.prettyString)
    //println("MinSeq: " + pr.minSequent)
  }

  "Constraint weakenings" should "output used arguments" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val fml = "x>1 & y>1 & z>1 -> [x:=1; ++ y:=*; ?y>5; {x'=1&x>2&y>2}]x>=0".asFormula

    //val fmls = ListBuffer[(PosInExpr, Formula)]()
    val fmls = ListBuffer[Formula]()
    val prgs = ListBuffer[Program]()

    val formAug = FormulaAugmentor("x>1 & y>1 & z>1 -> [x:=1; ++ y:=*; ?y>5; {x'=1&x>2&y>2}]x>=0".asFormula)

    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = e match {
        case Test(q) if q != True => fmls.appendAll(formulaSimplifications(q).map(simp => formAug.replaceAt(p, Test(simp)))); Left(None);
        case ODESystem(ogODE, q) if q != True => fmls.appendAll(formulaSimplifications(q).map(simp => formAug.replaceAt(p, ODESystem(ogODE, simp)))); Left(None);
        case c => Left(None)
      }
      override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
        case Imply(pre, Box(prog, f)) => fmls.appendAll(formulaSimplifications(pre).map(simp => formAug.replaceAt(p, Imply(simp, Box(prog,f))))); Left(None);
        case c => Left(None)
      }
      // NOTE TODO negation over everything might mess things up?
      /*

      override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
        case (q) if q != True => fmls.appendAll(formulaSimplifications(q)); Left(None);
        case ODESystem(_, q) if q != True => fmls.appendAll(formulaSimplifications(q)); Left(None);
        case c => Left(None)

      } */
    }, fml)

    println("simps: " + fmls)
    println("prgs: " + prgs)

    //val pr = proveBy(seq, minAuto)
    //println("After" + pr.prettyString)
    //println("MinSeq: " + pr.minSequent)
  }



}
