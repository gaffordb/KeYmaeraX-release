package edu.cmu.cs.ls.keymaera.tactics

//@todo minimize imports

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.AlphaConversionHelper.replace
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.AxiomTactic.{uncoverAxiomT,axiomLookupBaseT}
import edu.cmu.cs.ls.keymaera.tactics.AxiomaticRuleTactics.{equivalenceCongruenceT,equationCongruenceT}
import edu.cmu.cs.ls.keymaera.tactics.ContextTactics.cutInContext
import edu.cmu.cs.ls.keymaera.tactics.EqualityRewritingImpl.equivRewriting
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.AxiomCloseT
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.{onBranch,lastAnte,lastSucc,locateTerm}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.{getFormula,getTerm}

import scala.collection.immutable.List

/**
 * @todo The tactics do not actually do this -- the AxiomNameT only got the "correct" direction in the new implementation.
 *       The atomize and aggregate tactics are out-of-date.
 * Contains the axiom tactics and wrapper tactics for syntactic derivation of formulas and terms.
 * The axiom tactics go both directions; for this reason, there are three tactics per axiom:
 *    - The AxiomNameT tactic is the actual axiom.
 *    - The AxiomNameAtomizeT tactic derives in the typical left-to-right direction; that is, it takes a derivative
 *      term and constructs a non-derivative term.
 *    - The AxiomNameAggregateT tactic goes in the typical right-to-left direction.
 *
 * There is some code duplication in this file, but I figured it is probably not the end of the for such fundamental
 * tactics to be implement on a stand-alone basis.
 *
 * Created by nfulton on 2/4/15.
 */
object SyntacticDerivationInContext {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section 1: "Derivatives" of Formulas
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "->' derive imply".
   *   (p -> q)' <-> (!p | q)'
   * End.
   */
  def ImplyDerivativeT: PositionTactic with ApplicableAtFormula =
    BinaryFormulaDerivativeT("->' derive imply", Imply.unapply, deriveImply)
  private def deriveImply(p: Formula, q: Formula) = FormulaDerivative(Or(Not(p), q))

  /*
   * Axiom "forall' derive forall".
   *   (\forall x. p(x))' <-> (\forall x. (p(x)'))
   * End.
   */
  def ForallDerivativeT: PositionTactic with ApplicableAtFormula = new PositionTactic("forall' derive forall") with ApplicableAtFormula {
    def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(Forall(_, _)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = applies(getFormula(s, p))

    override def apply(p: Position): Tactic = {
      def axiomInstance(fml: Formula): Formula = fml match {
        case FormulaDerivative(Forall(vars, phi)) => Equiv(fml, Forall(vars, FormulaDerivative(phi)))
        case _ => False
      }
      uncoverAxiomT("forall' derive forall", axiomInstance, _ => ForallDerivativeBaseT)(p)
    }
  }
  /** Base tactic for forall derivative */
  private def ForallDerivativeBaseT: PositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(FormulaDerivative(Forall(vars, p)), _) =>
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        SubstitutionPair(aP, p) :: Nil
    }

    val aX = Variable("x", None, Real)
    def alpha(fml: Formula): PositionTactic = fml match {
      case Equiv(FormulaDerivative(Forall(vars, p)), _) =>
        assert(vars.length == 1, "Only quantifiers over single variable supported")
        if (vars.head.name != aX.name || vars.head.index != aX.index) {
          new PositionTactic("Alpha") {
            override def applies(s: Sequent, p: Position): Boolean = s(p) match {
              case Equiv(FormulaDerivative(Forall(_, _)), _) => true
              case _ => false
            }

            override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
              override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
                Some(globalAlphaRenamingT(vars.head.name, vars.head.index, aX.name, aX.index))

              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
          }
        } else NilPT
    }

    def axiomInstance(fml: Formula, axiom: Formula): Formula = fml match {
      case Equiv(FormulaDerivative(Forall(vars, p)), _) =>
        assert(vars.length == 1, "Only quantifiers over single variable supported")
        if (vars.head.name != aX.name || vars.head.index != aX.index) replace(axiom)(aX, vars.head.asInstanceOf[Variable])
        else axiom
    }
    axiomLookupBaseT("forall' derive forall", subst, alpha, axiomInstance)
  }

  /*
   * Axiom "&' derive and".
   *   (p & q)' <-> ((p') & (q'))
   * End.
   */
  def AndDerivativeT: PositionTactic with ApplicableAtFormula =
    BinaryFormulaDerivativeT("&' derive and", And.unapply, deriveAnd)
  private def deriveAnd(p: Formula, q: Formula) = And(FormulaDerivative(p), FormulaDerivative(q))

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "|' derive or".
   *   (p | q)' <-> ((p') & (q'))
   * End.
   */
  def OrDerivativeT: PositionTactic with ApplicableAtFormula =
    BinaryFormulaDerivativeT("|' derive or", Or.unapply, deriveOr)
  private def deriveOr(p: Formula, q: Formula) = And(FormulaDerivative(p), FormulaDerivative(q))

  /**
   * Unapplies binary formula &, |, ->, <->
   * @param m The unapply method, one of &, |, ->, <->.unapply
   * @tparam T The manifest (implicit by m).
   */
  class BinaryFormulaUnapplyer[T: Manifest](m: T => Option[(Formula, Formula)]) {
    def unapply(a: Any): Option[(Formula, Formula)] = {
      if (manifest[T].runtimeClass.isInstance(a)) m(a.asInstanceOf[T]) else None
    }
  }

  def BinaryFormulaDerivativeT[T: Manifest](axiomName: String,
                                            bin: T => Option[(Formula, Formula)],
                                            derive: (Formula, Formula) => Formula) =
      new PositionTactic(axiomName) with ApplicableAtFormula {
    val BFUnapplier = new BinaryFormulaUnapplyer(bin)

    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(BFUnapplier(_,_)) => true
      //      case BFUnapplier(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && applies(getFormula(s, p))

    override def apply(pos: Position): Tactic = {
      def axiomInstance(fml: Formula): Formula = fml match {
        case FormulaDerivative(BFUnapplier(p, q)) => Equiv(fml, derive(p, q))
        case _ => False
      }
      uncoverAxiomT(axiomName, axiomInstance, _ => BinaryFormulaDerivativeBaseT(axiomName, bin))(pos)
    }
  }

  private def BinaryFormulaDerivativeBaseT[T: Manifest](axiomName: String,
                                                        bin: T => Option[(Formula, Formula)]) = {
    val BFUnapplier = new BinaryFormulaUnapplyer(bin)
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(FormulaDerivative(BFUnapplier(p, q)), _) =>
        val aP = ApplyPredicate(Function("p", None, Real, Bool), Anything)
        val aQ = ApplyPredicate(Function("q", None, Real, Bool), Anything)
        SubstitutionPair(aP, p) :: SubstitutionPair(aQ, q) :: Nil
    }
    axiomLookupBaseT(axiomName, subst, _ => NilPT, (f, ax) => ax)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // @TODO A lot of things are missing from the axiom file...

  /*
   * Axiom "=' derive =".
   *   (s = t)' <-> ((s') = (t'))
   * End.
   */
  def EqualsDerivativeT: PositionTactic with ApplicableAtFormula =
    BinaryRelationDerivativeT("=' derive =", Equals.unapply, deriveEquals)
  private def deriveEquals(s: Sort, f: Term, g: Term) = Equals(s, Derivative(f.sort, f), Derivative(g.sort, g))

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom ">=' derive >=".
   *   (s >= t)' <-> ((s') >= (t'))
   * End.
   */
  def GreaterEqualDerivativeT: PositionTactic with ApplicableAtFormula =
    BinaryRelationDerivativeT(">=' derive >=", GreaterEqual.unapply, deriveGreaterEqual)
  private def deriveGreaterEqual(s: Sort, f: Term, g: Term) = GreaterEqual(s, Derivative(f.sort, f), Derivative(g.sort, g))

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom ">' derive >".
   *   (s > t)' <-> ((s') >= (t'))
   * End.
   */
  def GreaterThanDerivativeT: PositionTactic with ApplicableAtFormula =
    BinaryRelationDerivativeT(">' derive >", GreaterThan.unapply, deriveGreaterThan)
  private def deriveGreaterThan(s: Sort, f: Term, g: Term) = GreaterEqual(s, Derivative(f.sort, f), Derivative(g.sort, g))

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "<=' derive <=".
   *   (s <= t)' <-> ((s') <= (t'))
   * End.
   */
  def LessEqualDerivativeT: PositionTactic with ApplicableAtFormula =
    BinaryRelationDerivativeT("<=' derive <=", LessEqual.unapply, deriveLessEqual)
  private def deriveLessEqual(s: Sort, f: Term, g: Term) = LessEqual(s, Derivative(f.sort, f), Derivative(g.sort, g))

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "<' derive <".
   *   (s < t)' <-> ((s') <= (t'))
   * End.
   */
  def LessThanDerivativeT : PositionTactic with ApplicableAtFormula =
    BinaryRelationDerivativeT("<' derive <", LessThan.unapply, deriveLessThan)
  private def deriveLessThan(s: Sort, f: Term, g: Term) = LessEqual(s, Derivative(f.sort, f), Derivative(g.sort, g))

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "!=' derive !=".
   *   (s != t)' <-> ((s') = (t'))
   * End.
   */
  def NotEqualsDerivativeT: PositionTactic with ApplicableAtFormula =
    BinaryRelationDerivativeT("!=' derive !=", NotEquals.unapply, deriveNotEquals)
  private def deriveNotEquals(s: Sort, f: Term, g: Term) = Equals(s, Derivative(f.sort, f), Derivative(g.sort, g))

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * Unapplies binary relations <, <=, =, !=, >=, >
   * @param m The unapply method, one of <, <=, =, !=, >=, or >.unapply
   * @tparam T The manifest (implicit by m).
   */
  class BinaryRelationUnapplyer[T: Manifest](m: T => Option[(Sort, Term, Term)]) {
    def unapply(a: Any): Option[(Sort, Term, Term)] = {
      if (manifest[T].runtimeClass.isInstance(a)) m(a.asInstanceOf[T]) else None
    }
  }

  /**
   * Base tactic for deriving binary relations <, <=, =, !=, >=, >.
   * @param axiomName The name of the axiom.
   * @param bin The unapply method of the relation.
   * @param derive A method to perform the syntactic derivation of the relation.
   * @tparam T The manifest (implicit by bin).
   * @return The tactic.
   */
  def BinaryRelationDerivativeT[T: Manifest](axiomName: String,
                                             bin: T => Option[(Sort, Term, Term)],
                                             derive: (Sort, Term, Term) => Formula) =
    new PositionTactic(axiomName) with ApplicableAtFormula {
      val BRUnapplier = new BinaryRelationUnapplyer(bin)

      override def applies(f: Formula): Boolean = f match {
        case FormulaDerivative(BRUnapplier(eqSort, s, t)) => true
        //      case BRDUnapplier(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
        case _ => false
      }

      override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && applies(getFormula(s, p))

      override def apply(p: Position): Tactic = new ConstructionTactic(name) {
        override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
          def axiomInstance(fml: Formula): Formula = fml match {
            case FormulaDerivative(BRUnapplier(eqSort, s, t)) =>
              Equiv(fml, derive(eqSort, s, t))
            case _ => False
          }
          Some(uncoverAxiomT(axiomName, axiomInstance, _ => BinaryRelationDerivativeBaseT(axiomName, bin))(p))
        }
      }
    }
  /** Base tactic for binary relation derivative */
  private def BinaryRelationDerivativeBaseT[T: Manifest](axiomName: String,
                                                         bin: T => Option[(Sort, Term, Term)]): PositionTactic = {
    val BRUnapplier = new BinaryRelationUnapplyer(bin)
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Equiv(FormulaDerivative(BRUnapplier(sort, s, t)), _) =>
        val aF = Apply(Function("f", None, sort, sort), Anything)
        val aG = Apply(Function("g", None, sort, sort), Anything)
        SubstitutionPair(aF, s) :: SubstitutionPair(aG, t) :: Nil

    }
    axiomLookupBaseT(axiomName, subst, _ => NilPT, (f, ax) => ax)
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section 2. Syntactic Total Derivation of Terms.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //@todo throughout this section, the <- direction applicability is disabled in comments because the Atomize/Aggregate thing isn't possible to implement without position tactics for terms.
  //@todo when re-enabliong these applies lines, uncomment and re-run the relevant tests in SyntacticDerivationTests

  /*
   * Axiom "c()' derive constant fn".
   *   c()' = 0
   * End.
   */
  def ConstantDerivativeT = new PositionTactic("c()' derive constant fn") with ApplicableAtTerm {
    override def applies(s: Sequent, p: Position): Boolean = applies(getTerm(s, p))
    override def applies(t: Term): Boolean = t match {
      case Derivative(Real, Number(_, _)) => true
      case Derivative(Real, Apply(Function(_, _, Unit, Real), Nothing)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getTerm(node.sequent, p) match {
        case t@Derivative(Real, Number(_, _)) =>
          val r = Number(0)
          val formulaCtxPos = findParentFormulaPos(node.sequent(p), p.inExpr)
          val termCtxPos = PosInExpr(p.inExpr.pos.drop(formulaCtxPos.pos.length))

          Some(cutInContext(Equals(Real, t, r), p) & onBranch(
            (cutShowLbl, lastSucc(cohideT) &
              equivalenceCongruenceT(formulaCtxPos) &
              equationCongruenceT(termCtxPos) & lastSucc(ConstantDerivativeBaseT)),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
          ))
        case t@Derivative(Real, Apply(Function(_, _, Unit, Real), Nothing)) =>
          val r = Number(0)
          val formulaCtxPos = findParentFormulaPos(node.sequent(p), p.inExpr)
          val termCtxPos = PosInExpr(p.inExpr.pos.drop(formulaCtxPos.pos.length))

          Some(cutInContext(Equals(Real, t, r), p) & onBranch(
            (cutShowLbl, lastSucc(cohideT) &
              equivalenceCongruenceT(formulaCtxPos) &
              equationCongruenceT(termCtxPos) & lastSucc(ConstantDerivativeBaseT)),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
          ))
      }
    }
  }

  def ConstantDerivativeBaseT = new PositionTactic("c()' derive constant fn") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Equals(_, Derivative(Real, Number(_, _)), _) => true
      case Equals(_, Derivative(Real, Apply(Function(_, _, Unit, Real), Nothing)), _) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case fml@Equals(_, Derivative(Real, s@Number(_, _)), _) =>
          val aC = Apply(Function("c", None, Unit, Real), Nothing)
          val subst = List(SubstitutionPair(aC, s))
          val axiom = Axiom.axioms.get("c()' derive constant fn") match { case Some(ax) => ax }

          Some(
            assertT(0,1) & uniformSubstT(subst, Map(fml -> axiom)) &
              lastSucc(assertPT(axiom)) &
              AxiomTactic.axiomT("c()' derive constant fn") & assertT(1,1) & lastAnte(assertPT(axiom)) & lastSucc(assertPT(axiom)) &
              AxiomCloseT)
        case fml@Equals(_, Derivative(Real, s@Apply(Function(_, _, Unit, Real), Nothing)), _) =>
          val aC = Apply(Function("c", None, Unit, Real), Nothing)
          val subst = List(SubstitutionPair(aC, s))
          val axiom = Axiom.axioms.get("c()' derive constant fn") match { case Some(ax) => ax }

          Some(
            assertT(0,1) & uniformSubstT(subst, Map(fml -> axiom)) &
              lastSucc(assertPT(axiom)) &
              AxiomTactic.axiomT("c()' derive constant fn") & assertT(1,1) & lastAnte(assertPT(axiom)) & lastSucc(assertPT(axiom)) &
              AxiomCloseT)
      }
    }
  }

  def findParentFormulaPos(f: Formula, p: PosInExpr): PosInExpr = {
    if (TacticHelper.isFormula(f, p)) p
    else findParentFormulaPos(f, PosInExpr(p.pos.init))
  }

  /*
   * Axiom "-' derive neg".
   *   (-s)' = -(s')
   * End.
   */
  def NegativeDerivativeT = new PositionTactic("-' derive neg") with ApplicableAtTerm {
    override def applies(s: Sequent, p: Position): Boolean = applies(getTerm(s, p))
    override def applies(t: Term): Boolean = t match {
      case Derivative(_,Neg(_,_)) => true
      //      case Neg(_,Derivative(_,_)) => true //@todo add term position derivatives and re-enable this case, then uncomment test cases.
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getTerm(node.sequent, p) match {
        case t@Derivative(dSort, Neg(nSort, s)) =>
          val r = Neg(nSort, Derivative(dSort, s))
          val formulaCtxPos = findParentFormulaPos(node.sequent(p), p.inExpr)
          val termCtxPos = PosInExpr(p.inExpr.pos.drop(formulaCtxPos.pos.length))

          Some(cutInContext(Equals(nSort, t, r), p) & onBranch(
            (cutShowLbl, lastSucc(cohideT) &
              equivalenceCongruenceT(formulaCtxPos) &
              equationCongruenceT(termCtxPos) & lastSucc(NegativeDerivativeBaseT)),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
          ))
      }
    }
  }

  def NegativeDerivativeBaseT = new PositionTactic("-' derive neg") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Equals(_, Derivative(_,Neg(_,_)), _) => true
      //      case Neg(_,Derivative(_,_)) => true //@todo add term position derivatives and re-enable this case, then uncomment test cases.
      case _ => false
    }


    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case fml@Equals(_, t@Derivative(dSort, Neg(nSort, s)), _) => {
          val sort = nSort; assert(nSort == dSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val subst = List(SubstitutionPair(aF, s))
          val axiom = Axiom.axioms.get("-' derive neg") match { case Some(f) => f }

          // return tactic
          Some(
            assertT(0,1) & uniformSubstT(subst, Map(fml -> axiom)) &
              lastSucc(assertPT(axiom)) &
              AxiomTactic.axiomT("-' derive neg") & assertT(1,1) & lastAnte(assertPT(axiom)) & lastSucc(assertPT(axiom)) &
              AxiomCloseT)
        }
        case fml@Equals(_, Neg(nSort, Derivative(dSort, s)), _) => {
          val sort = nSort; assert(nSort == dSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          val subst = List(SubstitutionPair(aF, s))
          val axiom = Axiom.axioms.get("-' derive neg") match { case Some(f) => f }

          // return tactic
          Some(
            assertT(0,1) & uniformSubstT(subst, Map(fml -> axiom)) &
              lastSucc(assertPT(axiom)) &
              AxiomTactic.axiomT("-' derive neg") & assertT(1,1) & lastAnte(assertPT(axiom)) & lastSucc(assertPT(axiom)) &
              AxiomCloseT)
        }
      }
    }
  }

  /*
   * Axiom "+' derive sum".
   *  (s + t)' = (s') + (t')
   * End.
   */
  def AddDerivativeT = BinaryDerivativeT("+' derive sum", Add.unapply, deriveSum)
  def deriveSum(s: Sort, lhs: Term, rhs: Term): Term = Add(s, Derivative(s, lhs), Derivative(s, rhs))

  /*
   * Axiom "-' derive minus".
   *   (s - t)' = (s') - (t')
   * End.
   */
  def SubtractDerivativeT = BinaryDerivativeT("-' derive minus", Subtract.unapply, deriveMinus)
  def deriveMinus(s: Sort, lhs: Term, rhs: Term): Term = Subtract(s, Derivative(s, lhs), Derivative(s, rhs))

  /*
   * Axiom "*' derive product".
   * (s * t)' = ((s')*t) + (s*(t'))
   * End.
   */
  def MultiplyDerivativeT = BinaryDerivativeT("*' derive product", Multiply.unapply, deriveProduct)
  def deriveProduct(s: Sort, lhs: Term, rhs: Term): Term = Add(s, Multiply(s, Derivative(s, lhs), rhs), Multiply(s, lhs, Derivative(s, rhs)))

  /*
   * Axiom "/' derive quotient".
   * (s / t)' = (((s')*t) - (s*(t'))) / (t^2)
   * End.
   */
  def DivideDerivativeT = BinaryDerivativeT("/' derive quotient", Divide.unapply, deriveDivision)
  def deriveDivision(s: Sort, lhs: Term, rhs: Term): Term = Divide(s, Subtract(s, Multiply(s, Derivative(s, lhs), rhs), Multiply(s, lhs, Derivative(s, rhs))), Exp(s, rhs, Number(2)))

  def PowerDerivativeT = BinaryDerivativeT("^' derive power", Exp.unapply, deriveExponential)
  def deriveExponential(s: Sort, lhs: Term, rhs: Term): Term = {
    assert(rhs != Number(0), "not power 0")
    Multiply(Real, Multiply(Real, rhs, Exp(Real, lhs, Subtract(Real, rhs, Number(1)))), Derivative(Real, lhs))
  }

  class BinaryUnapplyer[T: Manifest](m: T => Option[(Sort, Term, Term)]) {
    def unapply(a: Any): Option[(Sort, Term, Term)] = {
      if (manifest[T].runtimeClass.isInstance(a)) m(a.asInstanceOf[T]) else None
    }
  }

  def BinaryDerivativeT[T: Manifest](axiomName: String,
                                     bin: T => Option[(Sort, Term, Term)],
                                     derive: (Sort, Term, Term) => Term) =
      new PositionTactic(axiomName) with ApplicableAtTerm {
    val BUnapplyer = new BinaryUnapplyer(bin)

    override def applies(s: Sequent, p: Position): Boolean = applies(getTerm(s, p))
    override def applies(t: Term): Boolean = t match {
      case Derivative(sort, BUnapplyer(sort2, _, _)) => true
      //      case BUnapplyer(_, Derivative(_,_), Derivative(_,_)) => true //@todo need tests when added.
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getTerm(node.sequent, p) match {
        case t@Derivative(sort, BUnapplyer(sort2, f, g)) =>
          val r = derive(sort, f, g)
          val formulaCtxPos = findParentFormulaPos(node.sequent(p), p.inExpr)
          val termCtxPos = PosInExpr(p.inExpr.pos.drop(formulaCtxPos.pos.length))

          Some(cutInContext(Equals(sort, t, r), p) & onBranch(
            (cutShowLbl, lastSucc(cohideT) &
              equivalenceCongruenceT(formulaCtxPos) &
              equationCongruenceT(termCtxPos) & lastSucc(BinaryDerivativeBaseT(axiomName, bin))),
            (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
          ))
      }
    }
  }

  def BinaryDerivativeBaseT[T: Manifest](axiomName: String,
                                         bin: T => Option[(Sort, Term, Term)]) = new PositionTactic(axiomName) {
    val BUnapplyer = new BinaryUnapplyer(bin)
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Equals(_, Derivative(sort, BUnapplyer(sort2, _, _)), _) => sort == sort2
      //      case BUnapplyer(_, Derivative(_,_), Derivative(_,_)) => true //@todo need tests when added.
      case _ => false
    }


    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getFormula(node.sequent, p) match {
        case fml@Equals(_, Derivative(dSort, BUnapplyer(aSort, f, g)), _) => {
          val sort = aSort; assert(dSort == aSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          // HACK
          val aG =
            if (axiomName == "^' derive power") Apply(Function("c", None, Unit, Real), Nothing)
            else Apply(Function("g", None, sort, sort), Anything)
          val subst = SubstitutionPair(aF, f) :: SubstitutionPair(aG, g) :: Nil

          val axiom = Axiom.axioms.get(axiomName) match { case Some(ax) => ax }

          // return tactic
          Some(
            assertT(0,1) & uniformSubstT(subst, Map(fml -> axiom)) &
              lastSucc(assertPT(axiom)) &
              AxiomTactic.axiomT(axiomName) & assertT(1,1) & lastAnte(assertPT(axiom)) & lastSucc(assertPT(axiom)) &
              AxiomCloseT)
        }
        case fml@Equals(_, BUnapplyer(aSort, Derivative(fSort, f), Derivative(gSort, g)), _) => {
          val sort = aSort; assert(aSort == fSort && aSort == gSort)

          val aF = Apply(Function("f", None, sort, sort), Anything)
          // HACK
          val aG =
            if (axiomName == "^' derive power") Apply(Function("c", None, Unit, Real), Nothing)
            else Apply(Function("g", None, sort, sort), Anything)
          val subst = SubstitutionPair(aF, f) :: SubstitutionPair(aG, g) :: Nil

          val axiom = Axiom.axioms.get(axiomName) match { case Some(ax) => ax }

          // return tactic
          Some(
            assertT(0,1) & uniformSubstT(subst, Map(fml -> axiom)) &
              lastSucc(assertPT(axiom)) &
              AxiomTactic.axiomT(axiomName) & assertT(1,1) & lastAnte(assertPT(axiom)) & lastSucc(assertPT(axiom)) &
              AxiomCloseT)
        }
      }
    }
  }

  trait ApplicableAtTerm {
    def applies(t : Term) : Boolean
  }
  trait ApplicableAtFormula {
    def applies(f : Formula) : Boolean
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Proof rule implementations
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  def SyntacticDerivationRulesT : Tactic =
    (SearchTacticsImpl.locateTerm(ConstantDerivativeT, inAnte = false) *) ~
    (SearchTacticsImpl.locateTerm(PowerDerivativeT, inAnte = false) *)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Atomize for Term Tactics @todo
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //@todo So that when this gets refactored we're not stuck changing a bunch of stuff.
  def NegativeDerivativeAtomizeT = NegativeDerivativeT
  def AddDerivativeAtomizeT      = AddDerivativeT
  def SubtractDerivativeAtomizeT = SubtractDerivativeT
  def MultiplyDerivativeAtomizeT = MultiplyDerivativeT
  def DivideDerivativeAtomizeT   = DivideDerivativeT
  def ConstantDerivativeAtomizeT = ConstantDerivativeT


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section: Wrapper tactic for term syntactic derivation
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * This list of *all* the atomizing TermAxiomTactics is used in the implementation of wrapper tactics.
   */
  val termDerivativeTactics : List[PositionTactic with ApplicableAtTerm] =
    NegativeDerivativeAtomizeT ::
      AddDerivativeAtomizeT ::
      SubtractDerivativeAtomizeT ::
      MultiplyDerivativeAtomizeT ::
      DivideDerivativeAtomizeT ::
      ConstantDerivativeAtomizeT ::
      Nil

  val formulaDerivativeTactics : List[PositionTactic with ApplicableAtFormula] =
    AndDerivativeT          ::
    OrDerivativeT           ::
    EqualsDerivativeT       ::
    GreaterEqualDerivativeT ::
    GreaterThanDerivativeT  ::
    LessEqualDerivativeT    ::
    LessThanDerivativeT     ::
    NotEqualsDerivativeT    ::
    ImplyDerivativeT        ::
    ForallDerivativeT       ::
    Nil

  /**
   * Finds a position in ``expression" where ``tactic" is applicable, or else returns None if ``tactic" is never applicable
   * in subexpressions of ``expression".
   *
   * This is used in the implementation of wrapper tactics.
   * @param expression
   * @param tactic
   */
  def findApplicablePositionForTermAxiom(expression : Expr, tactic : ApplicableAtTerm) : Option[(PosInExpr, Term)] = {
    val traversal = new ExpressionTraversalFunction {
      var mPosition : Option[PosInExpr] = None
      var mTerm : Option[Term] = None

      override def preT(p:PosInExpr, t:Term) = {
        if(tactic.applies(t)) {
          mPosition = Some(p);
          mTerm = Some(t);
          println("Found applicable tactic: " + tactic + " which applies to: " + expression) //@todo added because this tactic diverged when wrapped in a star for - examples.
          Left(Some(ExpressionTraversal.stop)) //stop once we find one applicable location.
        }
        else{
          Left(None)
        }
      }
    }

    expression match {
      case expression : Formula => ExpressionTraversal.traverse(traversal, expression)
      case expression : Term => ExpressionTraversal.traverse(traversal, expression)
      case expression : Program => ExpressionTraversal.traverse(traversal, expression)
      case _ => ???
    }

    (traversal.mPosition, traversal.mTerm) match {
      case (Some(p:PosInExpr), Some(t:Term)) => Some((p,t))
      case (None,None) => None
      case _ => ???
    }
  }

  def formulaContainsModality(f : Formula) : Option[(PosInExpr, Formula)] = {
    val fn = new ExpressionTraversalFunction {
      var thePair : Option[(PosInExpr, Formula)] = None
      override def preF(p : PosInExpr, f : Formula) = {
        val matches : Boolean = f match {
          case Modality(_,_) => true
          case BoxModality(_,_) => true
          case DiamondModality(_,_) => true
          case _ => false
        }
        if(matches) {thePair = Some( (p,f) ); Left(Some(ExpressionTraversal.stop))}
        else Left(None)
      }
    }
    ExpressionTraversal.traverse(fn,f)
    fn.thePair
  }

  /**
   * The wrapper tactic for total synactic derivation of *terms*.
   * In a single step, this tactic finds *one* location where *one* of the atomizing term derivative rewrites applies,
   * and then applies that tactic.
   */
  def TermSyntacticDerivationT = new PositionTactic("Total Syntactic Derivation of Terms") {
    //@todo this is wrong b/c what if we're applying in ^A -> [pi;](^^x > 0)' where ^^ is the term pos and ^ the formula pos?
    //@todo better but not quite right; what if we have something like ^[pi;]a -> ^^b?

    def applies(s : Sequent, p : Position) : Boolean = {
      appliesRegardlessOfContext(s,p) && !formulaContainsModality(s(p)).isDefined
    }

    //@todo move this into SyntacticDerivationT I guess...
    def appliesRegardlessOfContext(s: Sequent, p: Position): Boolean = {
      def tacticApplies(tactic : ApplicableAtTerm) = findApplicablePositionForTermAxiom(s(p), tactic) match {
        case Some(_) => true
        case None => false
      }

      termDerivativeTactics.foldLeft(false)((b, tat : PositionTactic with ApplicableAtTerm) => {
        tacticApplies(tat) || b
      }) || findApplicablePositionForTermAxiom(s(p), PowerDerivativeT).isDefined
    }

    /**
     * @todo this code is kind of complicated and probably deserves some refactoring.
     *       The formula version is much cleaner .
     */
    override def apply(pos: Position): Tactic = new ConstructionTactic(name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        /**
         * Returns a list of positions, together with the first applicable tactic at each position.
         */
        def firstApplicableTacticForEachPosition(seq : IndexedSeq[Formula]) : Seq[(PositionTactic with ApplicableAtTerm, Int, PosInExpr)] = {
          seq.zipWithIndex.map(p => {
            val formula = p._1
            val index: Int = p._2

            val tacticAndPos : Option[(PositionTactic with ApplicableAtTerm, PosInExpr)] = {
              //Check each of the tactics to determine if any apply.
              def findApplicablePosInFormula(tactic : ApplicableAtTerm) : Option[PosInExpr] = {
                findApplicablePositionForTermAxiom(formula, tactic) match {
                  case Some((posInExpr, term)) => Some(posInExpr)
                  case None => None
                }
              }

              val applicableTactics = termDerivativeTactics.map(t => findApplicablePosInFormula(t) match {
                case Some(posInExpr) => Some(t,posInExpr)
                case None => None
              }).filter(_.isDefined)

              if(applicableTactics.length == 0) {
                None
              }
              else {
                applicableTactics.last //just the first applicable tactic.
              }
            }

            tacticAndPos match {
              case Some((tactic:PositionTactic with ApplicableAtTerm, posInExpr:PosInExpr)) => Some(tactic, index, posInExpr)
              case None => None
            }
          }).filter(_.isDefined).map(_.get)
        }

        //First check the ante for any applicable tactics and positions; if there is one, return that one.
        //Else move on to the succ and so the same thing.
        val antePositions = firstApplicableTacticForEachPosition(node.sequent.ante)
        if(antePositions.length > 0) {
          val elmt      = antePositions.last
          val tactic    = elmt._1
          val anteIndex = elmt._2
          val posInExpr = elmt._3
          val position  = AntePosition(anteIndex, posInExpr)

          Some(tactic(position))
        }
        else {
          val succPositions = firstApplicableTacticForEachPosition(node.sequent.succ)
          if(succPositions.length > 0) {
            val elmt      = succPositions.last
            val tactic    = elmt._1
            val anteIndex = elmt._2
            val posInExpr = elmt._3
            Some(tactic(SuccPosition(anteIndex, posInExpr)))
          }
          else {
            None
          }
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }



  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section: Wrapper tactic for formula syntactic derivation
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def FormulaSyntacticDerivationT = new PositionTactic("Formula Syntactic Derivation") {
    override def applies(s: Sequent, p: Position): Boolean = {
      formulaDerivativeTactics.map(t => findApplicablePositionForFormulaDerivativeAxiom(s(p), t) match {
        case Some(_) => true
        case None    => false
      }).reduce(_ | _)
    }

    override def apply(p:Position) : Tactic = new ConstructionTactic("Formula Syntactic Derivation") {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val applicableTactics : Seq[(PositionTactic, PosInExpr)] =
          formulaDerivativeTactics.map(t => (t, findApplicablePositionForFormulaDerivativeAxiom(node.sequent(p), t))).
            filter(_._2.isDefined).map(p => (p._1, p._2.get._1))
        if (applicableTactics.length > 0) {
          val tactic    = applicableTactics.last._1
          val posInExpr = applicableTactics.last._2
          return Some(tactic(if (p.isAnte) AntePosition(p.index, posInExpr) else SuccPosition(p.index, posInExpr)))
        }
        assert(!applicable(node), "tactic signalled applicability, but about to return None")
        None
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }

    def findApplicablePositionForFormulaDerivativeAxiom(expression : Expr, tactic : PositionTactic with ApplicableAtFormula) : Option[(PosInExpr, Formula)] = {
      val traversal = new ExpressionTraversalFunction {
        var mPosition : Option[PosInExpr] = None
        var mFormula : Option[Formula]    = None

        override def preF(p:PosInExpr, f:Formula) = {
          if(tactic.applies(f)) {
            mPosition = Some(p);
            mFormula  = Some(f);

            Left(Some(ExpressionTraversal.stop)) //stop once we find one applicable location.
          }
          else{
            Left(None)
          }
        }
      }

      expression match {
        case expression : Formula => ExpressionTraversal.traverse(traversal, expression)
        case expression : Term    => ExpressionTraversal.traverse(traversal, expression)
        case expression : Program => ExpressionTraversal.traverse(traversal, expression)
        case _ => ???
      }

      (traversal.mPosition, traversal.mFormula) match {
        case (Some(p:PosInExpr), Some(f:Formula)) => Some((p,f))
        case (None,None) => None
        case _ => ???
      }
    }
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section: Syntactic derivation of constants and monomials.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /**
   * @todo I cannot believe that this does not exist somewhere already.
   */
  def getTermAtPosition(s : Sequent, p : Position) : Option[Term] = {
    val fn = new ExpressionTraversalFunction {
      var retVal : Option[Term] = None
      override def preT(pie : PosInExpr, t : Term) = {
        if(p.inExpr == pie) { //yummy
          retVal = Some(t)
          Left(Some(ExpressionTraversal.stop))
        }
        else Left(None)
      }
    }
    ExpressionTraversal.traverse(fn, s(p))
    fn.retVal
  }

  def MonomialAndConstantDerivationT = new PositionTactic("Derive monomial and constant") {
    override def applies(s: Sequent, p: Position): Boolean = !formulaContainsModality(s(p)).isDefined && {getTermAtPosition(s,p) match {
      case Some(Derivative(_, Number(_))) => true
      case Some(Derivative(_, exp:Exp)) => true
      case _ => false
    }}

    override def apply(p: Position): Tactic = PowerDerivativeT(p) ~ ConstantDerivativeT(p)
  }

  def MonomialAndConstantInContextDerivationT = new PositionTactic("Derive monomial and context in context") {
    override def applies(s: Sequent, p: Position): Boolean = {
      formulaContainsModality(s(p)).isDefined && {getTermAtPosition(s,p) match {
        case Some(Derivative(_, Number(_))) => true
        case Some(Derivative(_, exp:Exp)) => true
        case _ => false
      }}
    }

    override def apply(p: Position): Tactic =  PowerDerivativeT(p) ~ ConstantDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section: Wrapper tactic for syntactic derivation
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  def SyntacticDerivationT = new PositionTactic("Formula Syntactic Derivation") {
//    //Formula derivatives are treated using the in context base class, but the term derivative rules require the K construction.
//    //Hence, SyntacticDerivativeTermAxiomsInContext.
//    //@todo FormulaSyntacticDerivationT does something mean -- it looks around for a place to apply itself internally. This should be done in locate tactics, not in the main tactic.
//    override def applies(s: Sequent, p: Position): Boolean = SyntacticDerivativeTermAxiomsInContext.SyntacticDerivativeInContextT.applies(s,p) | FormulaSyntacticDerivationT.applies(s,p)
//
//    override def apply(p: Position): Tactic = (FormulaSyntacticDerivationT(p) *) ~ (SyntacticDerivativeTermAxiomsInContext.SyntacticDerivativeInContextT(p) *)
//  }


  /**
   * @todo this is just brokwn. Needs to apply at position, not everywhere... But that's an interface change, so for the moment I'll leave as-is.
   */
  def SyntacticDerivationT = new PositionTactic("Single Step of Total Syntactic Derivation") {
    import scala.language.postfixOps
    override def applies(s: Sequent, p: Position): Boolean = FormulaSyntacticDerivationT.applies(s, p) || TermSyntacticDerivationT.appliesRegardlessOfContext(s,p) || MonomialAndConstantDerivationT.applies(s,p) || MonomialAndConstantInContextDerivationT.applies(s,p) //@todo oh dear... should move this applies logic into SyntacticDerivativeTermAxiomsInContext.SyntacticDerivativeInContextT

    override def apply(p: Position): Tactic = (locate(FormulaSyntacticDerivationT)*) &
      assertT(!containsFormulaDerivative(_), "Formula derivative left unhandled by FormulaSyntacticDerivationT") &
      (locateTerm(SyntacticDerivativeTermAxiomsInContext.SyntacticDerivativeInContextT, inAnte = false)*) &
      (locateTerm(TermSyntacticDerivationT, inAnte = false) *) &
      assertT(!containsTermDerivative(_), "Term derivative left unhandled by TermSyntacticDerivationT") &
      (locateTerm(MonomialAndConstantDerivationT, inAnte = false) *) &
      assertT(containsOnlyVariableDerivatives(_), "Syntactic derivation left monomial or constant unhandled")

    private def containsFormulaDerivative(s: Sequent): Boolean =
      s.ante.exists(containsFormulaDerivative) || s.succ.exists(containsFormulaDerivative)

    private def containsFormulaDerivative(f: Formula): Boolean = {
      var containsFd = false
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, frm: Formula): Either[Option[StopTraversal], Formula] = frm match {
          case FormulaDerivative(_) => containsFd = true; Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, f)
      containsFd
    }

    private def containsTermDerivative(s: Sequent): Boolean =
      s.ante.exists(containsTermDerivative) || s.succ.exists(containsTermDerivative)

    private def containsTermDerivative(f: Formula): Boolean = {
      var containsTd = false
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
          case Derivative(_, _: Variable) => Left(None)
          case Derivative(_, _: Exp) => Left(None)
          case Derivative(_, _) => containsTd = true; Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, f)
      containsTd
    }

    private def containsOnlyVariableDerivatives(s: Sequent): Boolean =
      s.ante.forall(containsOnlyVariableDerivatives) && s.succ.forall(containsOnlyVariableDerivatives)

    private def containsOnlyVariableDerivatives(f: Formula): Boolean = {
      var onlyPrimitiveDerivatives = true
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
          case Derivative(_, _: Variable) => Left(None)
          case Derivative(_, _) => onlyPrimitiveDerivatives = false; Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, f)
      onlyPrimitiveDerivatives
    }

  }
}
