/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfoRegistry.{unren, unsure}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics.allInstantiateInverse
import edu.cmu.cs.ls.keymaerax.macros._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, RenUSubst}
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDB, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import org.apache.logging.log4j.scala.Logging

import scala.collection.{immutable, mutable}
import scala.collection.immutable._
import scala.reflect.runtime.{universe => ru}

/**
 * Database of Derived Axioms.
 *
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
 * @note To simplify bootstrap and avoid dependency management, the proofs of the derived axioms are
 *       written with explicit reference to other scala-objects representing provables (which will be proved on demand)
 *       as opposed to by referring to the names, which needs a map canonicalName->tacticOnDemand.
 * @note Lemmas are lazy vals, since their proofs may need a fully setup prover with QE
  * @note Derived axioms use the Provable facts of other derived axioms in order to avoid initialization cycles with AxiomInfo's contract checking.
 */


object DerivedAxioms extends Logging {

  val DerivedAxiomProvableSig = ProvableSig//NoProofTermProvable
  /** Database for derived axioms */
  val derivedAxiomDB: LemmaDB = LemmaDBFactory.lemmaDB

  type LemmaID = String

  /** Look up a core axiom from [[Provable.axioms]] and wrap it into a Lemma */
  private def coreAxiom(name: String): CoreAxiomInfo = {
    CoreAxiomInfo(name)
  }

  /** A Provable proving the derived axiom/rule named id (convenience) */
  def derivedAxiomOrRule(name: String): ProvableSig = {
    val lemmaName = DerivationInfo(name) match {
      case si: StorableInfo => si.storedName
      case _ => throw new IllegalArgumentException(s"Axiom or rule $name is not storable")
    }
    require(derivedAxiomDB.contains(lemmaName), "Lemma " + lemmaName + " should already exist in the derived axioms database.\n" +
      "Follow configuration instructions after restarting KeYmaera X with\n  java -jar keymaerax.jar")
    derivedAxiomDB.get(lemmaName).getOrElse(throw new IllegalArgumentException("Lemma " + lemmaName + " for derived axiom/rule " + name + " should have been added already")).fact
  }

  private val AUTO_INSERT: Boolean = true

  /** Derive an axiom from the given provable, package it up as a Lemma and make it available */
  private[btactics] def derivedFact(name: String, fact: ProvableSig, storedNameOpt: Option[String] = None): Lemma = {
    val storedName = storedNameOpt match {
      case Some(storedName) => storedName
      case None =>
        try {
          DerivedAxiomInfo(name).storedName
        } catch {
          case _: Throwable => throw new Exception(s"Derived axiom info for $name needs to exist or codeName needs to be explicitly passed")
        }
    }
    require(fact.isProved, "only proved Provables would be accepted as derived axioms: " + name + " got\n" + fact)
    val lemmaName = storedName // DerivedAxiomInfo.toStoredName(name)
    val npt = ElidingProvable(fact.underlyingProvable)
    val alternativeFact =
      if (ProvableSig.PROOF_TERMS_ENABLED) {
        TermProvable(npt, AxiomTerm(lemmaName))
      } else {
        npt
      }
    // create evidence (traces input into tool and output from tool)
    val evidence = ToolEvidence(immutable.List("input" -> npt.toString, "output" -> "true")) :: Nil
    // Makes it so we have the same provablesig when loading vs. storing
    val lemma = Lemma(alternativeFact, Lemma.requiredEvidence(alternativeFact, evidence), Some(lemmaName))
    if (!AUTO_INSERT) {
      lemma
    } else {
      /* @todo BUG does not work at the moment because lemmaDB adds some evidence to the lemmas and thus equality
      * (and thus contains) no longer means what this code thinks it means. */
      // first check whether the lemma DB already contains identical lemma name
      val lemmaID = if (derivedAxiomDB.contains(lemmaName)) {
        // identical lemma contents with identical name, so reuse ID
        derivedAxiomDB.get(lemmaName) match {
          case Some(storedLemma) =>
            if(storedLemma != lemma) {
              throw new IllegalStateException("Prover already has a different lemma filed under the same name " + derivedAxiomDB.get(lemmaName) + " (lemma " + name + " stored in file name " + lemmaName + ") instead of " + lemma )
            } else {
              lemma.name.get
            }
          case None => lemma.name.get
        }
      } else {
        derivedAxiomDB.add(lemma)
      }
      derivedAxiomDB.get(lemmaID).get
    }
  }

  private[btactics] def derivedRule(name: String, fact: ProvableSig, codeNameOpt: Option[String]): Lemma = {
    // create evidence (traces input into tool and output from tool)
    val evidence = ToolEvidence(immutable.List("input" -> fact.toString, "output" -> "true")) :: Nil
    val codeName = codeNameOpt match {
      case Some(codeName) => codeName
      case None =>
        try {
          DerivedRuleInfo(name).codeName
        } catch {
          case _: Throwable => throw new Exception("Derived rule info needs to exist or codeName needs to be explicitly passed")
        }
    }
    val lemmaName = DerivedAxiomInfo.toStoredName(codeName)
    val lemma = Lemma(fact, Lemma.requiredEvidence(fact, evidence), Some(lemmaName))
    if (!AUTO_INSERT) {
      lemma
    } else {
      // first check whether the lemma DB already contains identical lemma name
      val lemmaID = if (derivedAxiomDB.contains(lemmaName)) {
        // identical lemma contents with identical name, so reuse ID
        if (derivedAxiomDB.get(lemmaName).contains(lemma)) lemma.name.get
        else {
           throw new IllegalStateException("Prover already has a different lemma filed under the same name " + derivedAxiomDB.get(lemmaName) + " (lemma " + name + " stored in file name " + lemmaName + ") instnead of " + lemma )
        }
      } else {
        derivedAxiomDB.add(lemma)
      }
      derivedAxiomDB.get(lemmaID).get
    }
  }

  private[btactics] def derivedRuleSequent(name: String, derived: => Sequent, tactic: => BelleExpr, codeNameOpt: Option[String] = None): Lemma = {
    val codeName = codeNameOpt match {
      case Some(codeName) => codeName
      case None =>
        try {
          DerivedRuleInfo(name).storedName
        } catch {
          case _: Throwable => throw new Exception("Derived rule info needs to exist or codeName needs to be explicitly passed")
        }
    }
    val storageName = DerivedAxiomInfo.toStoredName(codeName)
    derivedAxiomDB.get(storageName) match {
      case Some(lemma) => lemma
      case None =>
        val witness = TactixLibrary.proveBy(derived, tactic)
        derivedRule(name, witness, codeNameOpt)
    }
  }

  /** Derive an axiom from the given provable, package it up as a Lemma and make it available */
  private[btactics] def derivedAxiomFromFact(canonicalName: String, derived: Formula, fact: ProvableSig, codeNameOpt: Option[String] = None): Lemma = {
    val codeName =
      codeNameOpt match {
        case Some(codeName) => codeName
        case None => try {
          DerivedAxiomInfo.apply(canonicalName).storedName
        } catch {
          case _: Throwable => throw new Exception(s"""Derived axiom info for   '$canonicalName' needs to exist or codeName needs to be explicitly passed""")
        }
      }
    val storedName = DerivedAxiomInfo.toStoredName(codeName)
    derivedFact(canonicalName, fact, Some(storedName)) ensuring(lem => lem.fact.conclusion == Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(derived)),
      "derivedAxioms's fact indeed proved the expected formula.\n" + derived + "\nproved by\n" + fact)
  }

  /** Derive an axiom for the given derivedAxiom with the given tactic, package it up as a Lemma and make it available */
  private[btactics] def derivedAxiom(canonicalName: String, derived: => Sequent, tactic: => BelleExpr, codeNameOpt: Option[String] = None): Lemma = {
    val codeName =
      codeNameOpt match {
        case Some(codeName) => codeName
        case None => try {
          DerivedAxiomInfo.apply(canonicalName).storedName
        } catch {
          case t: Throwable => throw new Exception(s"Derived axiom info for $canonicalName needs to exist or codeName needs to be explicitly passed")
        }
      }
    val storedName = DerivedAxiomInfo.toStoredName(codeName)
    derivedAxiomDB.get(storedName) match {
      case Some(lemma) => lemma
      case None =>
        val witness = TactixLibrary.proveBy(derived, tactic)
        assert(witness.isProved, "tactics proving derived axioms should produce proved Provables: " + canonicalName + " got\n" + witness)
        derivedFact(canonicalName, witness, Some(storedName))
    }
  }

  /** Derive an axiom for the given derivedAxiom with the given tactic, package it up as a Lemma and make it available */
  private[btactics] def derivedFormula(name: String, derived: Formula, tactic: => BelleExpr, codeNameOpt: Option[String] = None): Lemma =
    derivedAxiom(name, Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(derived)), tactic, codeNameOpt)

  private val x = Variable("x_", None, Real)
  private val px = PredOf(Function("p_", None, Real, Bool), x)
  private val pany = UnitPredicational("p_", AnyArg)
  private val qx = PredOf(Function("q_", None, Real, Bool), x)
  private val qany = UnitPredicational("q_", AnyArg)
  private val fany = UnitFunctional("f_", AnyArg, Real)
  private val gany = UnitFunctional("g_", AnyArg, Real)
  private val ctxt = Function("ctx_", None, Real, Real) // function symbol
  private val ctxf = Function("ctx_", None, Real, Bool) // predicate symbol
  private val context = Function("ctx_", None, Bool, Bool) // predicational symbol

  /** populates the derived lemma database with all of the lemmas in the case statement above.*/
  private[keymaerax] def prepopulateDerivedLemmaDatabase() = {
    require(AUTO_INSERT, "AUTO_INSERT should be on if lemma database is being pre-populated.")

    val lemmas = getClass.getDeclaredFields.filter(f => classOf[Lemma].isAssignableFrom(f.getType))
    val fns = lemmas.map(_.getName)

    val mirror = ru.runtimeMirror(getClass.getClassLoader)
    // access the singleton object
    val moduleMirror = mirror.reflectModule(ru.typeOf[DerivedAxioms.type].termSymbol.asModule)
    val im = mirror.reflect(moduleMirror.instance)

    //@note lazy vals have a "hidden" getter method that does the initialization
    val fields = fns.map(fn => ru.typeOf[DerivedAxioms.type].member(ru.TermName(fn)).asMethod.getter.asMethod)
    val fieldMirrors = fields.map(im.reflectMethod)

    var failures: mutable.Buffer[(String,Throwable)] = mutable.Buffer()
    fieldMirrors.indices.foreach(idx => {
      try {
        fieldMirrors(idx)()
      } catch {
        case e: Throwable =>
          failures += (fns(idx) -> e)
          logger.warn("WARNING: Failed to add derived lemma.", e)
      }
    })
    if (failures.nonEmpty)
      throw new Exception(s"WARNING: Encountered ${failures} failures when trying to populate DerivedAxioms database. Unable to derive:\n" + failures.map(_._1).mkString("\n"), failures.head._2)
  }


  //***************
  // Core Axioms   see [[AxiomBase]]
  //***************

  // Hybrid Programs / Hybrid Games

  //@note default key = 0::Nil, recursor = (Nil)::Nil for direct reduction of LHS to RHS without substructure.
  @Axiom(("<·>", "<.>"), formula = "<span class=\"k4-axiom-key\">&not;[a]&not;P</span>↔&langle;a&rangle;P", unifier = "linear")
  val diamond = coreAxiom("<> diamond")
  @Axiom("[:=]", formula = "<span class=\"k4-axiom-key\">[x:=e]p(x)</span>↔p(e)", unifier = "full")
  val assignbAxiom = coreAxiom("[:=] assign")
  @Axiom("[:=]=", formula = "<span class=\"k4-axiom-key\">[x:=e]P</span>↔∀x(x=e→P)",
    key = 0::Nil, recursor = (Nil)::(0::1::Nil)::Nil)
  val assignbeq = coreAxiom("[:=] assign equality")
  @Axiom("[:=]", formula = "<span class=\"k4-axiom-key\">[x:=x]P</span>↔P")
  val selfassignb = coreAxiom("[:=] self assign")
  @Axiom(("[:=]", "[:=]"), unifier = "full", formula = "<span class=\"k4-axiom-key\">[x':=c]p(x')</span>↔p(c)")
  val Dassignb = coreAxiom("[':=] differential assign")
  @Axiom("[:*]", formula = "<span class=\"k4-axiom-key\">[x:=*]p(x)</span>↔∀x p(x)")
  val randomb = coreAxiom("[:*] assign nondet")
  @Axiom("[?]", formula = "<span class=\"k4-axiom-key\">[?Q]P</span>↔(Q→P)", unifier = "linear",
    key = 0::Nil, recursor = (1::Nil)::Nil)
  val testb = coreAxiom("[?] test")
  @Axiom(("[∪]", "[++]"), formula = "<span class=\"k4-axiom-key\">[a∪b]P</span>↔[a]P∧[b]P", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  val choiceb = coreAxiom("[++] choice")
  @Axiom("[;]", formula = "<span class=\"k4-axiom-key\">[a;b]P</span>↔[a][b]P", unifier = "linear",
    key = 0::Nil, recursor = (1::Nil)::(Nil)::Nil)
  val composeb = coreAxiom("[;] compose")
  @Axiom("[*]", formula = "<span class=\"k4-axiom-key\">[a*]P</span>↔P∧[a][a*]P", unifier = "linear",
    key = 0::Nil, recursor = (1::Nil)::Nil)
  val iterateb = coreAxiom("[*] iterate")

  // Differential Equations

  // @TODO: Old AxiomInfo calls DWeakening
  @Axiom("DW base", unifier = "linear",
    key = Nil, recursor = Nil)
  val DWbase = coreAxiom("DW base")
  @Axiom("DE", formula = "<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]P</span>↔[x'=f(x)&Q][x':=f(x)]P",
    key = 0::Nil, recursor = (1::Nil)::(Nil)::Nil)
  val DE = coreAxiom("DE differential effect")
  @Axiom("DE", formula = "<span class=\"k4-axiom-key\">[{x'=F,c&Q}]P</span>↔[{c,x'=F&Q}][x':=f(x)]P",
    key = 0::Nil, recursor = (1::Nil)::(Nil)::Nil)
  val DEs = coreAxiom("DE differential effect (system)")
  /* @todo soundness requires only vectorial x in p(||) */
  @Axiom("DI", formula = "(<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]P</span>↔[?Q]P)←(Q→[{x'=f(x)&Q}](P)')", unifier = "linear",
    key = 1::0::Nil, recursor=(Nil)::Nil)
  val DIequiv = coreAxiom("DI differential invariance")
  @Axiom("DG", formula = "<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]P</span>↔∃y [{x'=f(x),y'=a*y+b&Q}]P")
  val DGa = coreAxiom("DG differential ghost")
  //@todo name: why inverse instead of universal?
  @Axiom("DG inverse differential ghost")
  val DGpp = coreAxiom("DG inverse differential ghost")
  @Axiom("DG inverse differential ghost implicational")
  val DGi = coreAxiom("DG inverse differential ghost implicational")
  @Axiom("DG", formula = "<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]P</span>↔∃y [{x'=f(x),y'=g()&Q}]P")
  val DGC = coreAxiom("DG differential ghost constant")
  @Axiom("DGa", formula = "<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]P</span>↔∀y [{x'=f(x),y'=g()&Q}]P")
  val DGCa = coreAxiom("DG differential ghost constant all")
  @Axiom("DS&", formula = "<span class=\"k4-axiom-key\">[{x'=c()&q(x)}]P</span> ↔ ∀t≥0 (∀0≤s≤t q(x+c()*s)) → [x:=x+c()*t;]P)",
    key = 0::Nil, recursor = (0::1::1::Nil)::(0::1::Nil)::(Nil)::Nil)
  val DS = coreAxiom("DS& differential equation solution")

  /* @todo: , commute should be derivable from this + ghost */
  @Axiom(",", unifier = "linear")
  val commaSort = coreAxiom(", sort")
  @Axiom(",", unifier = "linear",
    key = 0::Nil, recursor = Nil)
  val commaCommute = coreAxiom(", commute")
  @Axiom("DX", unifier = "linear",
    key = 0::Nil, recursor = (1::Nil)::Nil)
  val DX = coreAxiom("DX differential skip")
  @Axiom("DIo >", unifier = "linear", formula = "(<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]g(x)>h(x)</span>↔[?Q]g(x)>h(x))←(Q→[{x'=f(x)&Q}](g(x)>h(x)→(g(x)>h(x))'))",
    key = 1::0::Nil, recursor = (Nil)::Nil)
  val DIogreater = coreAxiom("DIo open differential invariance >")
  @Axiom("DMP", formula = "(<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]P</span>←[{x'=f(x)&R}]P)←[{x'=f(x)&Q}](Q→R)", inputs = "R:formula",
    key = 1::1::Nil /*@todo, recursor = (0::Nil)::(Nil)::Nil*/)
  val DMP = coreAxiom("DMP differential modus ponens")

  @Axiom("Uniq", formula = "<x'=f(x)&Q}>P ∧ <x'=f(x)&R>P → <x'=f(x)&Q∧R>P")
  val Uniq = coreAxiom("Uniq uniqueness")
  /* @note soundness requires no primes in f(||) (guaranteed by data structure invariant) */
  @Axiom("Cont", formula = "e>0 → <span class=\"k4-axiom-key\"><x'=f(x),t'=1&e>0>t≠0</span>",
    key = 1::Nil, recursor=(Nil)::Nil)
  val Cont = coreAxiom("Cont continuous existence")
  @Axiom("RI& >=")
  val RIclosedgeq = coreAxiom("RI& closed real induction >=")

  /* DIFFERENTIAL AXIOMS */

  @Axiom(("c()'", "c()'"), formula = "<span class=\"k4-axiom-key\">(c)'</span>=0", unifier = "linear",
    key = 0::Nil, recursor=Nil)
  val Dconst = coreAxiom("c()' derive constant fn")
  @Axiom("x'", formula = "<span class=\"k4-axiom-key\">(x)'</span>=x'", unifier = "linear",
    key = 0::Nil, recursor=Nil)
  val Dvar = coreAxiom("x' derive var")
  @Axiom(("-'", "-'"), formula = "<span class=\"k4-axiom-key\">(-f(x))'</span>=-(f(x))'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::Nil)
  val Dneg = coreAxiom("-' derive neg")
  @Axiom(("+'", "+'"), formula = "<span class=\"k4-axiom-key\">(f(x)+g(x))'</span>=f(x)'+g(x)'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  val Dplus = coreAxiom("+' derive sum")
  @Axiom(("-'", "-'"), formula = "<span class=\"k4-axiom-key\">(f(x)-g(x))'</span>=f(x)'-g(x)'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  val Dminus = coreAxiom("-' derive minus")
  @Axiom(("·'", "*'"), formula = "<span class=\"k4-axiom-key\">(f(x)·g(x))'</span>=(f(x))'·g(x)+f(x)·(g(x))'", unifier = "linear",
    key = 0::Nil, recursor = (0::0::Nil)::(1::1::Nil)::Nil)
  val Dtimes = coreAxiom("*' derive product")
  @Axiom(("/'", "/'"), formula = "<span class=\"k4-axiom-key\">(f(g)/g(x))'</span>=(g(x)·(f(x))-f(x)·(g(x))')/g(x)<sup>2</sup>", unifier = "linear",
    key = 0::Nil, recursor = (0::0::0::Nil)::(0::1::1::Nil)::Nil)
  val Dquotient = coreAxiom("/' derive quotient")
  @Axiom(("∘'", "o'"), formula = "[y:=g(x)][y':=1](<span class=\"k4-axiom-key\">(f(g(x)))'</span>=(f(y))'·(g(x))'",
    key = 1::1::0::Nil, recursor = (1::1::Nil)::(1::Nil)::(Nil)::Nil)
  val Dcompose = coreAxiom("chain rule")
  @Axiom(("^'", "^'"), formula = "<span class=\"k4-axiom-key\">(f(g)^n)'</span>=n·f(g)^(n-1)·(f(g))'←n≠0", unifier = "linear",
    key = 1::0::Nil, recursor = (1::Nil)::Nil)
  val Dpower = coreAxiom("^' derive power")
  @Axiom(("='", "='"), formula = "<span class=\"k4-axiom-key\">(f(x)=g(x))'</span>↔f(x)'=g(x)'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  val Dequal = coreAxiom("=' derive =")
  @Axiom(("≥'", ">='"), formula = "<span class=\"k4-axiom-key\">(f(x)≥g(x))'</span>↔f(x)'≥g(x)'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  val Dgreaterequal = coreAxiom(">=' derive >=")
  @Axiom(("≤'", "<='"), formula = "<span class=\"k4-axiom-key\">(f(x)≤g(x))'</span>↔f(x)'≤g(x)'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  val Dlessequal = coreAxiom("<=' derive <=")
  @Axiom(("<'", "<'"), formula = "<span class=\"k4-axiom-key\">(f(x)<g(m))'</span>↔f(x)'≤g(x)'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  val Dless = coreAxiom("<' derive <")
  @Axiom(("≠'", "!='"), formula = "<span class=\"k4-axiom-key\">(f(x)≠g(x))'</span>↔f(x)'=g(x)'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  val Dnotequal = coreAxiom("!=' derive !=")
  @Axiom(("∧'", "&'"), formula = "<span class=\"k4-axiom-key\">(P&Q)'</span>↔P'∧Q'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  val Dand = coreAxiom("&' derive and")
  @Axiom(("∨'", "|'"), formula = "<span class=\"k4-axiom-key\">(P|Q)'</span>↔P'∧Q'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  val Dor = coreAxiom("|' derive or")
  @Axiom(("∀'", "forall'"), formula = "<span class=\"k4-axiom-key\">(∀x p(x))'</span>↔∀x (p(x))'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::Nil)
  val Dforall = coreAxiom("forall' derive forall")
  @Axiom(("∃'", "exists'"), formula = "<span class=\"k4-axiom-key\">(∃x p(x))'</span>↔∀x (p(x))'", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::Nil)
  val Dexists = coreAxiom("exists' derive exists")

  /* HYBRID PROGRAMS / GAMES */

  @Axiom(("<d>", "<d>"), formula = "<span class=\"k4-axiom-key\">&langle;a<sup>d</sup>&rangle;P</span>↔¬&langle;a&rangle;¬P", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::Nil)
  val duald = coreAxiom("<d> dual")

  @Axiom("VK", formula = "(p→<span class=\"k4-axiom-key\">[a]p</span>)←[a]⊤",
    key = 1::1::Nil, recursor = (Nil)::Nil)
  val VK = coreAxiom("VK vacuous")
  @Axiom("[]T", formula = "<span class=\"k4-axiom-key\">[a]⊤</span>", unifier = "linear",
    key = Nil, recursor = Nil)
  val boxTrue = coreAxiom("[]T system")
  @Axiom("K", formula = "[a](P→Q) → ([a]P → <span class=\"k4-axiom-key\">[a]Q</span>)", unifier = "linear",
    key = 1::1::Nil, recursor = (Nil)::Nil)
  val K = coreAxiom("K modal modus ponens")
  //@note the tactic I has a codeName and belleExpr, but there's no tactic that simply applies the I-> axiom, because its sole purpose is to derive the stronger equivalence form
  @Axiom(("I<sub>→</sub>", "Iind"), formula = "P∧[a<sup>*</sup>](P→[a]P)→<span class=\"k4-axiom-key\">[a<sup>*</sup>]P</span>", displayLevel = "internal")
  val Iind = coreAxiom("I induction")

  /* FIRST-ORDER QUANTIFIER AXIOMS */

  @Axiom(("∀d", "alld"), formula = "<span class=\"k4-axiom-key\">¬∃x ¬P</span> ↔ ∀x P")
  val alld = coreAxiom("all dual")
  @Axiom(("∀e","alle"), formula = "<span class=\"k4-axiom-key\">∀x P</span> → P",
    key = 0::Nil, recursor = (Nil)::Nil)
  lazy val alle = coreAxiom("all eliminate")


  //***************
  // Derived Axioms
  //***************

  // semantic renaming cases

  /** Semantically renamed
    * {{{Axiom "[:=] assign equality y"
    *    [y_:=f();]p(||) <-> \forall y_ (y_=f() -> p(||))
    * End.
    * }}}
    * @note needs semantic renaming
    */
  @Axiom("[:=]=y", codeName = "assignbeqy")
  val assignbEquality_y = derivedAxiomFromFact("[:=] assign equality y",
    "[y_:=f();]p(||) <-> \\forall y_ (y_=f() -> p(||))".asFormula,
    ProvableSig.axioms("[:=] assign equality")(URename("x_".asVariable, "y_".asVariable, semantic = true)))

  /** Semantically renamed
    * {{{Axiom "[:=] self assign y"
    *   [y_:=y_;]p(||) <-> p(||)
    * End.
    * }}}
    * @note needs semantic renaming
    */
  @Axiom("[:=]y", "selfassignby")
  lazy val selfAssign_y = derivedAxiomFromFact("[:=] self assign y",
    "[y_:=y_;]p(||) <-> p(||)".asFormula,
    ProvableSig.axioms("[:=] self assign")(URename("x_".asVariable,"y_".asVariable,semantic=true)))

  /** Semantically renamed
    * {{{Axiom "DE differential effect (system) y"
    *    // @note Soundness: f(||) cannot have ' by data structure invariant. AtomicODE requires explicit-form so f(||) cannot have differentials/differential symbols
    *    [{y_'=f(||),c&q(||)}]p(||) <-> [{c,y_'=f(||)&q(||)}][y_':=f(||);]p(||)
    * End.
    * }}}
    * @note needs semantic renaming
    */
  @Axiom("DEsysy", codeName = "DEsysy", formula = "<span class=\"k4-axiom-key\">[{y'=F,c&Q}]P</span>↔[{c,y'=F&Q}][y':=f(x)]P"
  ,  key = 0::Nil, recursor = (1::Nil)::Nil::Nil)
  lazy val DEdifferentialEffectSystem_y = derivedAxiomFromFact("DE differential effect (system) y",
    "[{y_'=f(||),c&q(||)}]p(||) <-> [{c,y_'=f(||)&q(||)}][y_':=f(||);]p(||)".asFormula,
    ProvableSig.axioms("DE differential effect (system)")(URename("x_".asVariable,"y_".asVariable,semantic=true)))

  /** Semantically renamed
    * {{{Axiom "all dual y"
    *    (!\exists y_ !p(||)) <-> \forall y_ p(||)
    * End.
    * }}}
    * @note needs semantic renaming
    */
  @Axiom(("∀d","alldy"), "alldy")
  lazy val allDual_y = derivedAxiomFromFact("all dual y",
    "(!\\exists y_ !p(||)) <-> \\forall y_ p(||)".asFormula,
    ProvableSig.axioms("all dual")(URename("x_".asVariable,"y_".asVariable,semantic=true)))

  /** Semantically renamed
    * {{{Axiom "all dual time"
    *    (!\exists t_ !p(||)) <-> \forall t_ p(||)
    * End.
    * }}}
    * @note needs semantic renaming
    */
  @Axiom(("∀d","alldt"), "alldt")
  lazy val allDual_time = derivedAxiomFromFact("all dual time",
    "(!\\exists t_ !p(||)) <-> \\forall t_ p(||)".asFormula,
    ProvableSig.axioms("all dual")(URename("x_".asVariable,"t_".asVariable,semantic=true)))

  /** Semantically renamed
    * {{{Axiom "all eliminate y"
    *   (\forall y_ p(||)) -> p(||)
    * End.
    * }}}
    * @note needs semantic renaming
    */
  @Axiom(("∀y","ally"), "ally")
  lazy val allEliminate_y = derivedAxiomFromFact("all eliminate y",
    "(\\forall y_ p(||)) -> p(||)".asFormula,
    ProvableSig.axioms("all eliminate")(URename("x_".asVariable,"y_".asVariable,semantic=true)))


  // derived axioms used in useAt itself, thus given as Provables not lemmas, just in case to avoid dependencies

  lazy val boxTrueTrue = TactixLibrary.proveBy(
    "[a{|^@|};]true <-> true".asFormula,
    equivR(1) <(closeT, cohideR(1) & byUS("[]T system")))

  lazy val impliesRightAnd = TactixLibrary.proveBy(
    "(p_()->q_()) & (p_()->r_()) <-> (p_() -> q_()&r_())".asFormula,
    TactixLibrary.prop)

  lazy val sameImpliesImplies = TactixLibrary.proveBy(
    "(p_()->q_()) -> (p_()->r_()) <-> (p_() -> (q_()->r_()))".asFormula,
    TactixLibrary.prop)

  lazy val factorAndRight = TactixLibrary.proveBy(
    "(q_()&p_()) & (r_()&p_()) <-> ((q_()&r_()) & p_())".asFormula,
    TactixLibrary.prop)

  lazy val factorAndLeft = TactixLibrary.proveBy(
    "(p_()&q_()) & (p_()&r_()) <-> (p_() & (q_()&r_()))".asFormula,
    TactixLibrary.prop)

  lazy val factorOrRight = TactixLibrary.proveBy(
    "(q_()|p_()) & (r_()|p_()) <-> ((q_()&r_()) | p_())".asFormula,
    TactixLibrary.prop)

  lazy val factorOrLeft = TactixLibrary.proveBy(
    "(p_()|q_()) & (p_()|r_()) <-> (p_() | (q_()&r_()))".asFormula,
    TactixLibrary.prop)

  lazy val factorImpliesOrRight = TactixLibrary.proveBy(
    "(q_()|p_()) -> (r_()|p_()) <-> ((q_()->r_()) | p_())".asFormula,
    TactixLibrary.prop)

  lazy val factorImpliesOrLeft = TactixLibrary.proveBy(
    "(p_()|q_()) -> (p_()|r_()) <-> (p_() | (q_()->r_()))".asFormula,
    TactixLibrary.prop)

  lazy val impliesMonAndLeft = TactixLibrary.proveBy(
    "(q_()->r_()) -> (q_()&p_() -> r_()&p_())".asFormula,
    TactixLibrary.prop)

  lazy val impliesMonAndRight = TactixLibrary.proveBy(
    "(q_()->r_()) -> (p_()&q_() -> p_()&r_())".asFormula,
    TactixLibrary.prop)

  lazy val trueOr = TactixLibrary.proveBy(
    "true | p_() <-> true".asFormula,
    TactixLibrary.prop)

  lazy val orTrue = TactixLibrary.proveBy(
    "p_() | true <-> true".asFormula,
    TactixLibrary.prop)


  lazy val ponensAndPassthrough_Imply = TactixLibrary.proveBy(
    "((p_() ->q_())&p_() -> q_()) <-> true".asFormula,
    TactixLibrary.prop)

  lazy val ponensAndPassthrough_Equiv = TactixLibrary.proveBy(
    "((p_()<->q_())&p_() -> q_()) <-> true".asFormula,
    TactixLibrary.prop)

  lazy val ponensAndPassthrough_coImply = TactixLibrary.proveBy(
    "((q_() ->p_())&q_() -> p_()) <-> true".asFormula,
    TactixLibrary.prop)

  lazy val ponensAndPassthrough_coEquiv = TactixLibrary.proveBy(
    "((p_()<->q_())&q_() -> p_()) <-> true".asFormula,
    TactixLibrary.prop)

  // derived rules

  /**
    * Rule "all generalization".
    * Premise p(||)
    * Conclusion \forall x p(||)
    * End.
    *
    * @derived from G or from [] monotone with program x:=*
    * @derived from Skolemize
    * @Note generalization of p(x) to p(||) as in Theorem 14
    */
  @DerivedRule(("all gen", "allgen"), "allGeneralize", premises = "|- P", conclusion = "|- \\forall x P")
  lazy val allGeneralize = derivedRuleSequent("all generalization",
    //(immutable.IndexedSeq(Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(pany))),
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("\\forall x_ p_(||)".asFormula)),
    useAt("[:*] assign nondet", PosInExpr(1::Nil))(1) &
      cut(Box(AssignAny(Variable("x_",None,Real)), True)) <(
        byUS(boxMonotone) & hide(-1)
        ,
        hide(1) & HilbertCalculus.boxTrue(1)
        )
  )

  /**
    * Rule "Goedel".
    * Premise p(||)
    * Conclusion [a;]p(||)
    * End.
    * {{{
    *       p(||)
    *   ----------- G
    *    [a{|^@|};]p(||)
    * }}}
    * @NOTE Unsound for hybrid games
    * @derived from M and [a]true
    */
  @DerivedRule("G", "Goedel", conclusion = "|- [a;]P", premises = "|- P")
  lazy val Goedel = derivedRuleSequent("Goedel",
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("[a_{|^@|};]p_(||)".asFormula)),
    cut("[a_{|^@|};]true".asFormula) <(
      // use
      byUS(boxMonotone) & hide(-1)
      ,
      // show
      hide(1) & HilbertCalculus.boxTrue(1)
      )
  )

  /**
    * {{{
    *   Axiom "V vacuous".
    *  p() -> [a{|^@|};]p()
    * End.
    * }}}
    * @note unsound for hybrid games
    */
  @Axiom(("V", "V"), codeName = "V", formula = "p→<span class=\"k4-axiom-key\">[a]p</span>", key = 1::Nil, recursor = Nil::Nil)
  lazy val vacuousAxiom = derivedAxiom("V vacuous",
    Sequent(IndexedSeq(), IndexedSeq("p() -> [a{|^@|};]p()".asFormula)),
    useAt("VK vacuous", PosInExpr(1::Nil))(1) &
    HilbertCalculus.boxTrue(1)
  )

  /**
    * {{{Axiom /*\\foralli */ "all instantiate"
    *    (\forall x_ p(x_)) -> p(f())
    * End.
    * }}}
    * @note Core axiom derivable thanks to [:=]= and [:=]
    */
  @Axiom(("∀inst","allInst"), "allInst", key = 0::Nil, recursor = Nil::Nil)
  lazy val allInstantiate = derivedFormula("all instantiate",
    "(\\forall x_ p(x_)) -> p(f())".asFormula,
    cutR("(\\forall x_ (x_=f()->p(x_))) -> p(f())".asFormula)(1) <(
      useAt("[:=] assign equality", PosInExpr(1::Nil))(1, 0::Nil) &
        useAt("[:=] assign")(1, 0::Nil) &
        implyR(1) & close(-1,1)
      ,
      CMon(PosInExpr(0::0::Nil)) &
        implyR(1) & implyR(1) & close(-1,1)
      )
    //      ------------refl
    //      p(f) -> p(f)
    //      ------------------ [:=]
    //    [x:=f]p(x) -> p(f)
    //   --------------------------------[:=]=
    //    \forall x (x=f -> p(x)) -> p(f)
    //   -------------------------------- CMon(p(x) -> (x=f->p(x)))
    //   \forall x p(x) -> p(f)
  )

  /**
    * {{{
    *   Axiom "vacuous all quantifier"
    *     (\forall x_ p()) <-> p()
    *   End.
    * }}}
    * @Note Half of this is a base axiom officially but already derives from [:*] and V
    */
  @Axiom(("V∀","allV"), "allV", key = 0::Nil, recursor = Nil::Nil)
  lazy val vacuousAllAxiom = derivedAxiom("vacuous all quantifier",
    Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ p()) <-> p()".asFormula)),
    useAt(equivExpand)(1) & andR(1) <(
      byUS("all eliminate")
      ,
      useAt("[:*] assign nondet", PosInExpr(1::Nil))(1, 1::Nil) &
      byUS(vacuousAxiom)
      )
  )


  /**
    * Rule "CT term congruence".
    * Premise f_(||) = g_(||)
    * Conclusion ctxT_(f_(||)) = ctxT_(g_(||))
    * End.
    *
    * @derived ("Could also use CQ equation congruence with p(.)=(ctx_(.)=ctx_(g_(x))) and reflexivity of = instead.")
    */
  @DerivedRule(("CT term congruence", "CTtermCongruence"), "CTtermCongruence", conclusion = "|- ctx_(f_(||)) = ctx_(g_(||))",
    premises = "|- f_(||) = g_(||)")
  lazy val CTtermCongruence =
    derivedRuleSequent("CT term congruence",
      Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("ctx_(f_(||)) = ctx_(g_(||))".asFormula)),
      cutR("ctx_(g_(||)) = ctx_(g_(||))".asFormula)(SuccPos(0)) <(
        byUS(equalReflex)
        ,
        equivifyR(1) &
          CQ(PosInExpr(0::0::Nil)) &
          useAt(equalCommute)(1)
      )
    )

  /**
    * Rule "[] monotone".
    * Premise p(||) ==> q(||)
    * Conclusion [a;]p(||) ==> [a;]q(||)
    * End.
    *
    * @derived useAt("<> diamond") & by("<> monotone")
    * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
    * @see "André Platzer. Differential Hybrid Games."
    * @note Notation changed to p instead of p_ just for the sake of the derivation.
    */
  @DerivedRule(("[] monotone", "[]monotone"), "monb", conclusion = "[a;]P |- [a;]Q", premises = "P |- Q")
  lazy val boxMonotone = derivedRuleSequent("[] monotone",
    Sequent(immutable.IndexedSeq("[a_;]p_(||)".asFormula), immutable.IndexedSeq("[a_;]q_(||)".asFormula)),
    useAt(boxAxiom, PosInExpr(1::Nil))(-1) & useAt(boxAxiom, PosInExpr(1::Nil))(1) &
      notL(-1) & notR(1) &
      by("<> monotone", USubst(
        SubstitutionPair(UnitPredicational("p_", AnyArg), Not(UnitPredicational("q_", AnyArg))) ::
          SubstitutionPair(UnitPredicational("q_", AnyArg), Not(UnitPredicational("p_", AnyArg))) :: Nil)) &
      notL(-1) & notR(1)
  )

  /**
    * Rule "[] monotone 2".
    * Premise q(||) ==> p(||)
    * Conclusion [a;]q(||) ==> [a;]p(||)
    * End.
    *
    * @derived useAt(boxMonotone) with p and q swapped
    * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
    * @see "André Platzer. Differential Hybrid Games."
    * @note Renamed form of boxMonotone.
    */
  @DerivedRule(("[] monotone 2", "[]monotone 2"), "monb2", conclusion = "[a;]Q |- [a;]P", premises = "Q |- P")
  lazy val boxMonotone2 = derivedRuleSequent("[] monotone 2",
    Sequent(immutable.IndexedSeq("[a_;]q_(||)".asFormula), immutable.IndexedSeq("[a_;]p_(||)".asFormula)),
    useAt(boxAxiom, PosInExpr(1::Nil))(-1) & useAt(boxAxiom, PosInExpr(1::Nil))(1) &
      notL(-1) & notR(1) &
      byUS("<> monotone") &
      //      ProofRuleTactics.axiomatic("<> monotone", USubst(
      //        SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), Not(PredOf(Function("q_", None, Real, Bool), Anything))) ::
      //          SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), Not(PredOf(Function("p_", None, Real, Bool), Anything))) :: Nil)) &
      notL(-1) & notR(1)
  )

  val v = Variable("x_", None, Real)
  val anonv = ProgramConst("a_", Except(v::Nil))
  val Jany = UnitPredicational("J", AnyArg)

  /**
    * Rule "con convergence flat".
    * Premisses: \exists x_ (x <= 0 & J(||)) |- P
    *            x_ > 0, J(||) |- <a{|x_|}><x_:=x_-1;> J(||)
    * Conclusion  \exists x_ J(||) |- <a{|x_|}*>P(||)
    * {{{
    *    \exists x_ (x_ <= 0 & J(x_)) |- P   x_ > 0, J(x_) |- <a{|x_|}>J(x_-1)
    *    ------------------------------------------------- con
    *     \exists x_ J(x_) |- <a{|x_|}*>P
    * }}}
    */
  @DerivedRule(("con flat", "conflat"), "conflat", conclusion = "J |- <a*>P",
    premises ="\\exists v (v<=0&J) |- P;; v > 0, J |- <a>J(v-1)")
  lazy val convergenceFlat =
    derivedRuleSequent("con convergence flat",
      Sequent(immutable.IndexedSeq(Exists(immutable.Seq(v), Jany)), immutable.IndexedSeq(Diamond(Loop(anonv), "p_(||)".asFormula))),
      cut(Diamond(Loop(anonv), Exists(immutable.Seq(v), And(LessEqual(v, Number(0)), Jany)))) <(
        hideL(-1) & mond
          // existsL(-1)
          //useAt("exists eliminate", PosInExpr(1::Nil))(-1) & andL(-1)
        ,
        hideR(1) & by(ProvableSig.rules("con convergence"))
        )
    )


  // derived axioms and their proofs

  /**
    * {{{Axiom "<-> reflexive".
    *  p() <-> p()
    * End.
    * }}}
    *
    * @Derived
    * @see [[equalReflex]]
    */
  @Axiom(("↔R","<->R"), "equivReflexive", unifier = "full")
  lazy val equivReflexiveAxiom = derivedFact("<-> reflexive",
    DerivedAxiomProvableSig.startProof(Sequent(IndexedSeq(), IndexedSeq("p_() <-> p_()".asFormula)))
    (EquivRight(SuccPos(0)), 0)
      // right branch
      (Close(AntePos(0),SuccPos(0)), 1)
      // left branch
      (Close(AntePos(0),SuccPos(0)), 0)
    , None
  )

  /** Convert <-> to two implications:
    * (p_() <-> q_()) <-> (p_()->q_())&(q_()->p_())
    */
  @Axiom(("↔2→←","<->2-><-"), "equivExpand", unifier = "full")
  lazy val equivExpand = derivedFormula("<-> expand",
    "(p_() <-> q_()) <-> (p_()->q_())&(q_()->p_())".asFormula, prop)

  /**
    * {{{Axiom "-> distributes over &".
    *  (p() -> (q()&r())) <-> ((p()->q()) & (p()->r()))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("→∧", "->&"), "implyDistAnd")
  lazy val implyDistAndAxiom = derivedAxiom("-> distributes over &",
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> (q_()&r_())) <-> ((p_()->q_()) & (p_()->r_()))".asFormula)),
    prop
  )

  /**
    * {{{Axiom "-> weaken".
    *  (p() -> q()) -> (p()&c() -> q())
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("→W","->W"), "implyWeaken")
  lazy val implWeaken = derivedAxiom("-> weaken",
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> q_()) -> ((p_()&c_()) -> q_())".asFormula)),
    prop
  )

  /**
    * {{{Axiom "-> distributes over <->".
    *  (p() -> (q()<->r())) <-> ((p()->q()) <-> (p()->r()))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("→↔","-><->"), "implyDistEquiv")
  lazy val implyDistEquivAxiom = derivedAxiom("-> distributes over <->",
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> (q_()<->r_())) <-> ((p_()->q_()) <-> (p_()->r_()))".asFormula)),
    prop
  )


  /**
    * CONGRUENCE AXIOMS (for constant terms)
    */


  /**
    * {{{Axiom "const congruence"
    *      s() = t() -> ctxT_(s()) = ctxT_(t())
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("CCE", "constCongruence", key = 1::Nil, recursor = Nil::Nil, unifier = "full")
  lazy val constCongruence: Lemma = derivedFormula("const congruence",
    "s() = t() -> ctxT_(s()) = ctxT_(t())".asFormula,
    allInstantiateInverse(("s()".asTerm, "x_".asVariable))(1) &
      by(proveBy("\\forall x_ (x_ = t() -> ctxT_(x_) = ctxT_(t()))".asFormula,
        useAt("[:=] assign equality", PosInExpr(1::Nil))(1) &
          useAt("[:=] assign")(1) &
          byUS(equalReflex)
      ))
  )

  /**
    * {{{Axiom "const formula congruence"
    *    s() = t() -> (ctxF_(s()) <-> ctxF_(t()))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("CCQ", "constFormulaCongruence", key = 1::Nil, recursor = Nil::Nil, unifier = "full")
  lazy val constFormulaCongruence: Lemma = derivedFormula("const formula congruence",
    "s() = t() -> (ctxF_(s()) <-> ctxF_(t()))".asFormula,
    allInstantiateInverse(("s()".asTerm, "x_".asVariable))(1) &
      by(proveBy("\\forall x_ (x_ = t() -> (ctxF_(x_) <-> ctxF_(t())))".asFormula,
        useAt("[:=] assign equality", PosInExpr(1::Nil))(1) &
          useAt("[:=] assign")(1) &
          byUS(equivReflexiveAxiom)
      ))
  )


  /**
    * {{{Axiom "!! double negation".
    *  (!(!p())) <-> p()
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("¬¬","!!"), formula ="¬¬p↔p", codeName ="doubleNegation", unifier = "linear")
  lazy val doubleNegationAxiom = derivedFact("!! double negation",
    DerivedAxiomProvableSig.startProof(Sequent(IndexedSeq(), IndexedSeq("(!(!p_())) <-> p_()".asFormula)))
    (EquivRight(SuccPos(0)), 0)
      // right branch
      (NotRight(SuccPos(0)), 1)
      (NotLeft(AntePos(1)), 1)
      (Close(AntePos(0),SuccPos(0)), 1)
      // left branch
      (NotLeft(AntePos(0)), 0)
      (NotRight(SuccPos(1)), 0)
      (Close(AntePos(0),SuccPos(0)), 0)
  )

  /**
    * {{{Axiom "vacuous all quantifier".
    *  (\forall x_ p()) <-> p()
    * End.
    * }}}
    *
    * @Derived from new axiom "p() -> (\forall x_ p())" and ""all instantiate" or "all eliminate".
    * @todo replace by weaker axiom in AxiomBase and prove it.
    */

  /**
    * {{{Axiom "exists dual".
    *   (!\forall x (!p(||))) <-> (\exists x p(||))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("∃d","existsd"), codeName ="existsDual", key = 0::Nil, recursor = Nil::Nil)
  lazy val existsDualAxiom = derivedAxiom("exists dual",
    Sequent(IndexedSeq(), IndexedSeq("(!\\forall x_ (!p_(||))) <-> \\exists x_ p_(||)".asFormula)),
    useAt("all dual", PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  @Axiom(("∃d","existsdy"), codeName ="existsDualy")
  lazy val existsDualAxiomy = derivedAxiom("exists dual y",
    Sequent(IndexedSeq(), IndexedSeq("(!\\forall y_ (!p_(||))) <-> \\exists y_ p_(||)".asFormula)),
    useAt(allDual_y, PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "!exists".
    *   (!\exists x (p(x))) <-> \forall x (!p(x))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("¬∃","!exists"), "notExists", "<span class=\"k4-axiom-key\">(¬∃x (p(x)))</span>↔∀x (¬p(x))"
  , key = 0::Nil, recursor = (0::Nil)::(Nil)::Nil)
  lazy val notExists = derivedAxiom("!exists",
    Sequent(IndexedSeq(), IndexedSeq("(!\\exists x_ (p_(x_))) <-> \\forall x_ (!p_(x_))".asFormula)),
    useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::0::0::Nil) &
      useAt("all dual")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "!all".
    *   (!\forall x (p(||))) <-> \exists x (!p(||))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("¬∀", "!all"), "notAll", "<span class=\"k4-axiom-key\">¬∀x (p(x)))</span>↔∃x (¬p(x))"
  , key = (0::Nil), recursor = (0::Nil)::Nil::Nil)
  lazy val notAll = derivedAxiom("!all",
    Sequent(IndexedSeq(), IndexedSeq("(!\\forall x_ (p_(||))) <-> \\exists x_ (!p_(||))".asFormula)),
    useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::0::0::Nil) &
      useAt(existsDualAxiom)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "![]".
    *   ![a;]p(x) <-> <a;>!p(x)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("¬[]","![]"), "notBox", key = 0::Nil, recursor = (1::Nil)::Nil::Nil, unifier = "linear")
  lazy val notBox = derivedAxiom("![]",
    Sequent(IndexedSeq(), IndexedSeq("(![a_;]p_(x_)) <-> (<a_;>!p_(x_))".asFormula)),
    useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::0::1::Nil) &
      useAt("<> diamond")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "!<>".
    *   !<a;>p(x) <-> [a;]!p(x)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("¬<>","!<>"), "notDiamond", key = 0::Nil, recursor = (1::Nil)::Nil::Nil, unifier = "linear")
  lazy val notDiamond = derivedAxiom("!<>",
    Sequent(IndexedSeq(), IndexedSeq("(!<a_;>p_(x_)) <-> ([a_;]!p_(x_))".asFormula)),
    useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::0::1::Nil) &
      useAt(boxAxiom)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )



  //***************
  // Derived Axioms
  //***************


  /**
    * {{{Axiom "all distribute".
    *   (\forall x (p(x)->q(x))) -> ((\forall x p(x))->(\forall x q(x)))
    * }}}
    */
  @Axiom(("∀→","all->"), "allDist")
  lazy val allDistributeAxiom = derivedAxiom("all distribute",
    Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ (p(x_)->q(x_))) -> ((\\forall x_ p(x_))->(\\forall x_ q(x_)))".asFormula)),
    implyR(1) & implyR(1) & allR(1) & allL(-2) & allL(-1) & prop)

  /**
    * {{{Axiom "all distribute".
    *   (\forall x (p(x)->q(x))) -> ((\forall x p(x))->(\forall x q(x)))
    * }}}
    */
  @Axiom(("∀→","all->"), "allDistElim")
  lazy val allDistributeElim = derivedAxiom("all distribute elim",
    Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ (p_(||)->q_(||))) -> ((\\forall x_ p_(||))->(\\forall x_ q_(||)))".asFormula)),
    implyR(1) & implyR(1) & ProofRuleTactics.skolemizeR(1) & useAt("all eliminate")(-1) & useAt("all eliminate")(-2) & prop)

  /**
    * {{{Axiom "all quantifier scope".
    *    (\forall x (p(x) & q())) <-> ((\forall x p(x)) & q())
    * End.
    * }}}
    *
    * @todo follows from "all distribute" and "all vacuous"
    */


  /**
    * {{{Axiom "[] box".
    *    (!<a;>(!p(||))) <-> [a;]p(||)
    * End.
    * }}}
    *
    * @note almost same proof as "exists dual"
    * @Derived
    */
  @Axiom(("[·]", "[.]"), formula = "<span class=\"k4-axiom-key\">&not;&langle;a&rangle;&not;P</span> ↔ &langle;a&rangle;P", codeName = "box",
    key = 0::Nil, recursor = Nil::Nil)
  lazy val boxAxiom = derivedAxiom("[] box",
    Sequent(IndexedSeq(), IndexedSeq("(!<a_;>(!p_(||))) <-> [a_;]p_(||)".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::1::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{
    *   Axiom "Kd diamond modus ponens".
    *     [a{|^@|};](p(||)->q(||)) -> (<a{|^@|};>p(||) -> <a{|^@|};>q(||))
    *   End.
    * }}}
    */
  @Axiom("Kd", "Kd")
  lazy val KdAxiom = derivedAxiom("Kd diamond modus ponens",
    Sequent(IndexedSeq(), IndexedSeq("[a{|^@|};](p(||)->q(||)) -> (<a{|^@|};>p(||) -> <a{|^@|};>q(||))".asFormula)),
    useExpansionAt("<> diamond")(1, 1::0::Nil) &
      useExpansionAt("<> diamond")(1, 1::1::Nil) &
      useAt(converseImply, PosInExpr(1::Nil))(1, 1::Nil) &
      useAt(converseImply, PosInExpr(0::Nil))(1, 0::1::Nil) &
      byUS("K modal modus ponens")
  )

  /**
    * {{{
    *   Axiom "Kd2 diamond modus ponens".
    *     [a{|^@|};]p(||) -> (<a{|^@|};>q(||) -> <a{|^@|};>(p(||)&q(||)))
    *   End.
    * }}}
    */
  @Axiom("Kd2", "Kd2")
  lazy val Kd2Axiom = derivedAxiom("Kd2 diamond modus ponens",
    Sequent(IndexedSeq(), IndexedSeq("[a{|^@|};]p(||) -> (<a{|^@|};>q(||) -> <a{|^@|};>(p(||)&q(||)))".asFormula)),
    useExpansionAt("<> diamond")(1, 1::0::Nil) &
      useExpansionAt("<> diamond")(1, 1::1::Nil) &
      useAt(DerivedAxioms.converseImply, PosInExpr(1::Nil))(1, 1::Nil) &
      useAt("K modal modus ponens", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt("K modal modus ponens", PosInExpr(1::Nil))(1) &
      useAt(proveBy("(p_() -> !(p_()&q_()) -> !q_()) <-> true".asFormula, prop))(1, 1::Nil) &
      byUS("[]T system") & TactixLibrary.done
  )

  /**
    * {{{Axiom "[]~><> propagation".
    *    [a;]p(||) & <a;>q(||) -> <a;>(p(||) & q(||))
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  @Axiom("[]~><>", "boxDiamondPropagation")
  lazy val boxDiamondPropagation =
    derivedAxiom("[]~><> propagation",
      Sequent(IndexedSeq(), IndexedSeq("([a_{|^@|};]p_(||) & <a_{|^@|};>q_(||)) -> <a_{|^@|};>(p_(||) & q_(||))".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::1::Nil) &
        useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
        cut("[a_{|^@|};]p_(||) & [a_{|^@|};]!(p_(||)&q_(||)) -> [a_{|^@|};]!q_(||)".asFormula) <(
          /* use */ prop,
          /* show */ hideR(1) &
          cut("[a_{|^@|};](p_(||) & !(p_(||)&q_(||)))".asFormula) <(
            /* use */ implyR(1) & hideL(-2) & /* monb fails renaming substitution */ implyRi & CMon(PosInExpr(1::Nil)) & prop,
            /* show */ implyR(1) & TactixLibrary.boxAnd(1) & prop
            )
          )
    )

  /**
    * {{{Axiom "[]~><> subst propagation".
    *    <a;>true -> ([a;]p(||) -> <a;>p(||))
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  @Axiom("[]~><> subst", "boxDiamondSubstPropagation")
  lazy val boxDiamondSubstPropagation: Lemma = derivedAxiom("[]~><> subst propagation",
    Sequent(IndexedSeq(), IndexedSeq("<a_{|^@|};>true -> ([a_{|^@|};]p(||) -> <a_{|^@|};>p(||))".asFormula)),
    cut("[a_{|^@|};]p(||) & <a_{|^@|};>true -> <a_{|^@|};>p(||)".asFormula) <(
      prop & done,
      hideR(1) & useAt(boxDiamondPropagation, PosInExpr(0::Nil))(1, 0::Nil) & useAt(andTrue)(1, 0::1::Nil) &
      prop & done
    )
  )

  /**
    * {{{Axiom "K1".
    *   [a;](p(||)&q(||)) -> [a;]p(||) & [a;]q(||)
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, K1 p. 26
    * @internal
    */
  private lazy val K1 = TactixLibrary.proveBy(//derivedAxiom("K1",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]p_(||) & [a_{|^@|};]q_(||)".asFormula)),
    implyR(1) & andR(1) <(
      useAt(boxSplitLeft, PosInExpr(0::Nil))(-1) & close,
      useAt(boxSplitRight, PosInExpr(0::Nil))(-1) & close
      )
  )

  /**
    * {{{Axiom "K2".
    *   [a;]p(||) & [a;]q(||) -> [a;](p(||)&q(||))
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, K2 p. 27
    *      @internal
    */
  private lazy val K2 = TactixLibrary.proveBy(//derivedAxiom("K2",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};]p_(||) & [a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||))".asFormula)),
    cut(/*(9)*/"([a_{|^@|};](q_(||)->p_(||)&q_(||)) -> ([a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||))))  ->  (([a_{|^@|};]p_(||) & [a_{|^@|};]q_(||)) -> [a_{|^@|};](p_(||)&q_(||)))".asFormula) <(
      /* use */ cut(/*(6)*/"[a_{|^@|};](q_(||) -> (p_(||)&q_(||)))  ->  ([a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||)))".asFormula) <(
      /* use */ modusPonens(AntePos(1), AntePos(0)) & close,
      /* show */ cohide(2) & byUS("K modal modus ponens")
      ),
      /* show */ cut(/*(8)*/"([a_{|^@|};]p_(||) -> [a_{|^@|};](q_(||) -> p_(||)&q_(||)))  ->  (([a_{|^@|};](q_(||)->p_(||)&q_(||)) -> ([a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||))))  ->  (([a_{|^@|};]p_(||) & [a_{|^@|};]q_(||)) -> [a_{|^@|};](p_(||)&q_(||))))".asFormula) <(
      /* use */ cut(/*(5)*/"[a_{|^@|};]p_(||) -> [a_{|^@|};](q_(||) -> p_(||)&q_(||))".asFormula) <(
      /* use */ modusPonens(AntePos(1), AntePos(0)) & close,
      /* show */ cohide(3) & useAt("K modal modus ponens", PosInExpr(1::Nil))(1) & useAt(implyTautology)(1, 1::Nil) & V(1) & close
      ),
      /* show */ cohide(3) & prop
      )
      )
  )

  /**
    * {{{Axiom "K modal modus ponens &".
    *    [a;](p_(||)->q_(||)) & [a;]p_(||) -> [a;]q_(||)
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  @Axiom("K&", "Kand", key = 1::1::Nil, recursor = Nil::Nil)
  lazy val Kand = derivedAxiom("K modal modus ponens &",
    Sequent(IndexedSeq(), IndexedSeq("[a{|^@|};](p_(||)->q_(||)) & [a{|^@|};]p_(||) -> [a{|^@|};]q_(||)".asFormula)),
    useAt(andImplies, PosInExpr(0::Nil))(1) &
    byUS("K modal modus ponens")
  )

  /**
    * {{{Axiom "&->".
    *    (A() & B() -> C()) <-> (A() -> B() -> C())
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("&->", "andImplies")
  lazy val andImplies = derivedAxiom("&->",
    Sequent(IndexedSeq(), IndexedSeq("(A_() & B_() -> C_()) <-> (A_() -> B_() -> C_())".asFormula)),
    prop)

  /**
    * {{{Axiom "[] split".
    *    [a;](p(||)&q(||)) <-> [a;]p(||)&[a;]q(||)
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, K3 p. 28
    */
  @Axiom(("[]∧", "[]^"), "boxAnd", "<span class=\"k4-axiom-key\">[a](P∧Q)</span>↔[a]P ∧ [a]Q"
  , key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil, unifier = "linear")
  lazy val boxAnd =
    derivedAxiom("[] split",
      Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) <-> [a_{|^@|};]p_(||)&[a_{|^@|};]q_(||)".asFormula)),
      equivR(1) <(
        useAt(K1, PosInExpr(1::Nil))(1) & close,
        useAt(K2, PosInExpr(1::Nil))(1) & close
      )
    )

  /**
    * {{{Axiom "[] conditional split".
    *    [a;](p(||)->q(||)&r(||)) <-> [a;](p(||)->q(||)) & [a;](p(||)->r(||))
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  @Axiom(("[]→∧", "[]->^"), "boxImpliesAnd", "<span class=\"k4-axiom-key\">[a](P→Q∧R)</span> ↔ [a](P→Q) ∧ [a](P→R)", unifier = "linear")
  lazy val boxImpliesAnd = derivedAxiom("[] conditional split",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](P_(||)->Q_(||)&R_(||)) <-> [a_{|^@|};](P_(||)->Q_(||)) & [a_{|^@|};](P_(||)->R_(||))".asFormula)),
    useAt(implyDistAndAxiom, PosInExpr(0::Nil))(1, 0::1::Nil) &
    useAt(boxAnd, PosInExpr(0::Nil))(1, 0::Nil) &
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "boxSplitLeft".
    *    [a;](p(||)&q(||)) -> [a;]p(||)
    * End.
    * }}}
    *
    * @Derived
    * @Note implements (1)-(5) of Cresswell, Hughes. A New Introduction to Modal Logic, K1
    *      @internal
    */
  private lazy val boxSplitLeft = {
    TactixLibrary.proveBy(//derivedAxiom("[] split left",
      Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]p_(||)".asFormula)),
      cut(/*(2)*/"[a_{|^@|};](p_(||)&q_(||) -> p_(||))".asFormula) <(
        /* use */ cut(/*(4)*/"[a_{|^@|};](p_(||)&q_(||)->p_(||)) -> ([a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]p_(||))".asFormula) <(
        /* use */ modusPonens(AntePos(0), AntePos(1)) & close,
        /* show */ cohide(2) & byUS("K modal modus ponens")
      ),
        /* show */ cohide(2) & useAt(PC1)(1, 1::0::Nil) & useAt(implySelf)(1, 1::Nil) & V(1) & close
      )
    )
  }

  /**
    * {{{Axiom "<> split".
    *    <a;>(p(||)|q(||)) <-> <a;>p(||)|<a;>q(||)
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  @Axiom(("<>∨","<>|"), "diamondOr", "<span class=\"k4-axiom-key\">&langle;a&rangle;(P∨Q)</span>↔&langle;a&rangle;P ∨ &langle;a&rangle;Q"
  , key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil, unifier = "linear")
  lazy val diamondOr = derivedAxiom("<> split",
    Sequent(IndexedSeq(), IndexedSeq("<a_{|^@|};>(p_(||)|q_(||)) <-> <a_{|^@|};>p_(||)|<a_{|^@|};>q_(||)".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::Nil) &
      useAt(notOr)(1, 0::0::1::Nil) &
      useAt(boxAnd)(1, 0::0::Nil) &
      useAt(notAnd)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<> partial vacuous".
    *    <a;>p(||) & q() <-> <a;>(p(||)&q())
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  @Axiom(("pVd","pVd"), "pVd")
  lazy val diamondPartialVacuous: Lemma = derivedAxiom("<> partial vacuous",
    Sequent(IndexedSeq(), IndexedSeq("(<a_{|^@|};>p_(||) & q_()) <-> <a_{|^@|};>(p_(||)&q_())".asFormula)),
      equivR(1) <(
        andL(-1) & useAt("<> diamond", PosInExpr(1::Nil))(1) & notR(1) &
        useAt("<> diamond", PosInExpr(1::Nil))(-1) & notL(-1) &
        useAt(notAnd)(-2, 1::Nil) & useAt(implyExpand, PosInExpr(1::Nil))(-2, 1::Nil) &
        useAt(converseImply)(-2, 1::Nil) & useAt(doubleNegationAxiom)(-2, 1::0::Nil) &
        useAt("K modal modus ponens", PosInExpr(0::Nil))(-2) & implyL(-2) <(V('Rlast) & closeId, closeId)
        ,
        useAt("<> diamond", PosInExpr(1::Nil))(-1) & useAt(notAnd)(-1, 0::1::Nil) &
        useAt(implyExpand, PosInExpr(1::Nil))(-1, 0::1::Nil) & notL(-1) &
        andR(1) <(
          useAt("<> diamond", PosInExpr(1::Nil))(1) & notR(1) & implyRi &
          useAt("K modal modus ponens", PosInExpr(1::Nil))(1) &
          useAt(proveBy("(!p() -> p() -> q()) <-> true".asFormula, prop))(1, 1::Nil) & byUS("[]T system")
          ,
          useAt(proveBy("!q_() -> (p_() -> !q_())".asFormula, prop), PosInExpr(1::Nil))(2, 1::Nil) &
          V(2) & notR(2) & closeId
        )
      )
  )

  /**
    * {{{Axiom "<> split left".
    *    <a;>(p(||)&q(||)) -> <a;>p(||)
    * End.
    * }}}
    *
    * @Derived
    *         @internal
    */
  private lazy val diamondSplitLeft = TactixLibrary.proveBy(//derivedAxiom("<> split left",
    Sequent(IndexedSeq(), IndexedSeq("<a_;>(p_(||)&q_(||)) -> <a_;>p_(||)".asFormula)),
    useAt(PC1)(1, 0::1::Nil) & useAt(implySelf)(1) & close
  )

  /**
    * {{{Axiom "boxSplitRight".
    *    [a;](p(||)&q(||)) -> q(||)
    * End.
    * }}}
    *
    * @Derived
    * @Note implements (6)-(9) of Cresswell, Hughes. A New Introduction to Modal Logic, K1
    *      @internal
    */
  private lazy val boxSplitRight = TactixLibrary.proveBy(//derivedAxiom("[] split right",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]q_(||)".asFormula)),
    cut(/*7*/"[a_{|^@|};](p_(||)&q_(||) -> q_(||))".asFormula) <(
      /* use */ cut(/*(8)*/"[a_{|^@|};](p_(||)&q_(||)->q_(||)) -> ([a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]q_(||))".asFormula) <(
      /* use */ modusPonens(AntePos(0), AntePos(1)) & close,
      /* show */ cohide(2) & byUS("K modal modus ponens")
      ),
      /* show */ cohide(2) & useAt(PC2)(1, 1::0::Nil) & useAt(implySelf)(1, 1::Nil) & V(1) & close
      )
  )

  /**
    * {{{Axiom ":= assign dual 2".
    *    <x:=f();>p(||) <-> [x:=f();]p(||)
    * End.
    * }}}
    *
    * @see [[assignDualAxiom]]
    */
  @Axiom(":=D", "assignDual2")
  lazy val assignDual2Axiom = derivedFormula(":= assign dual 2",
    "<x_:=f();>p(||) <-> [x_:=f();]p(||)".asFormula,
    useAt("[:=] self assign", PosInExpr(1::Nil))(1, 0::1::Nil) &
      useAt(assigndAxiom)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
    // NOTE alternative proof:
    //    useAt("[:=] assign equality exists")(1, 1::Nil) &
    //      useAt("<:=> assign equality")(1, 0::Nil) &
    //      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<:=> assign equality".
    *    <x:=f();>p(||) <-> \exists x (x=f() & p(||))
    * End.
    * }}}
    *
    * @Derived from [:=] assign equality, quantifier dualities
    * @Derived by ":= assign dual" from "[:=] assign equality exists".
    */
  @Axiom("<:=>", "assigndEquality",
    key = 0::Nil, recursor = Nil::(0::1::Nil)::Nil)
  lazy val assigndEqualityAxiom = derivedAxiom("<:=> assign equality",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f_();>p_(||) <-> \\exists x_ (x_=f_() & p_(||))".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt(existsDualAxiom, PosInExpr(1::Nil))(1, 1::Nil) &
      useAt(notAnd)(1, 1::0::0::Nil) &
      useAt(implyExpand, PosInExpr(1::Nil))(1, 1::0::0::Nil) &
      CE(PosInExpr(0::Nil)) &
      byUS("[:=] assign equality")
  )

  /**
    * {{{Axiom "[:=] assign equality exists".
    *   [x:=f();]p(||) <-> \exists x (x=f() & p(||))
    * End.
    * }}}
    *
    * @Derived by ":= assign dual" from "<:=> assign equality".
    * @todo does not derive yet
    */
  @Axiom(("[:=]", "[:=] assign exists"), "assignbequalityexists")
  lazy val assignbExistsAxiom = derivedFormula("[:=] assign equality exists",
    "[x_:=f();]p(||) <-> \\exists x_ (x_=f() & p(||))".asFormula,
    useAt(assignDual2Axiom, PosInExpr(1::Nil))(1, 0::Nil) &
      byUS(assigndEqualityAxiom)
    //      useAt(assigndEqualityAxiom, PosInExpr(1::Nil))(1, 1::Nil) &
    //        //@note := assign dual is not applicable since [v:=t()]p(v) <-> <v:=t()>p(t),
    //        //      and [v:=t()]p(||) <-> <v:=t()>p(||) not derivable since clash in allL
    //        useAt(":= assign dual")(1, 1::Nil) & byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "[:=] assign exists".
    *  [x_:=f_();]p_(||) -> \exists x_ p_(||)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("[:=]∃","[:=]exists"), "assignbexists")
  lazy val assignbImpliesExistsAxiom = derivedAxiom("[:=] assign exists",
    Sequent(IndexedSeq(), IndexedSeq("[x_:=f_();]p_(||) -> \\exists x_ p_(||)".asFormula)),
//    useAt(existsAndAxiom, PosInExpr(1::Nil))(1, 1::Nil)
//      & byUS("[:=] assign equality exists")
    useAt(assignbExistsAxiom, PosInExpr(0::Nil))(1, 0::Nil) &
    byUS(existsAndAxiom)
  )

  /**
    * {{{Axiom "[:=] assign all".
    *  \forall x_ p_(||) -> [x_:=f_();]p_(||)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("[:=]∀","[:=]all"), "assignball")
  lazy val forallImpliesAssignbAxiom = derivedAxiom("[:=] assign all",
    Sequent(IndexedSeq(), IndexedSeq("\\forall x_ p_(||) -> [x_:=f_();]p_(||)".asFormula)),
    //    useAt(existsAndAxiom, PosInExpr(1::Nil))(1, 1::Nil)
    //      & byUS("[:=] assign equality exists")
      useAt("[:=] assign equality", PosInExpr(0::Nil))(1, 1::Nil) &
      byUS(forallImpliesAxiom)
  )

  /**
    * {{{Axiom "\\exists& exists and".
    *  \exists x_ (q_(||) & p_(||)) -> \exists x_ (p_(||))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("∃∧", "existsAnd")
  lazy val existsAndAxiom =
    derivedAxiom("\\exists& exists and",
    Sequent(IndexedSeq(), IndexedSeq("\\exists x_ (q_(||) & p_(||)) -> \\exists x_ (p_(||))".asFormula)),
    /*implyR(1) &*/ CMon(PosInExpr(0::Nil)) & prop // & andL(-1) & closeId//(-2,1)
  )

  /**
    * {{{Axiom "\\forall-> forall implies".
    *  \forall x_ p_(||) -> \forall x_ (q_(||) -> p_(||))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("∀→", "forallImplies")
  lazy val forallImpliesAxiom =
    derivedAxiom("\\forall-> forall implies",
      Sequent(IndexedSeq(), IndexedSeq("\\forall x_ p_(||) -> \\forall x_ (q_(||) -> p_(||))".asFormula)),
      /*implyR(1) &*/ CMon(PosInExpr(0::Nil)) & prop // & andL(-1) & closeId//(-2,1)
    )

  /**
    * {{{Axiom "<:=> assign equality all".
    *    <x:=f();>p(||) <-> \forall x (x=f() -> p(||))
    * End.
    * }}}
    */
  @Axiom("<:=>", "assigndEqualityAll", key = 0::Nil, recursor = Nil::(0::1::Nil)::Nil)
  lazy val assigndEqualityAllAxiom = derivedAxiom("<:=> assign equality all",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f_();>p_(||) <-> \\forall x_ (x_=f_() -> p_(||))".asFormula)),
    useAt(assignDual2Axiom, PosInExpr(0::Nil))(1, 0::Nil) &
      byUS("[:=] assign equality")
  )

  /**
    * {{{Axiom "<:=> assign".
    *    <v:=t();>p(v) <-> p(t())
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("<:=>", "assignd", "<span class=\"k4-axiom-key\">&langle;x:=e&rangle;p(x)</span>↔p(e)",
    key = 0::Nil, recursor = Nil::Nil, unifier = "full")
  lazy val assigndAxiom = derivedAxiom("<:=> assign",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f();>p(x_) <-> p(f())".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[:=] assign")(1, 0::0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<:=> self assign".
    *    <x_:=x_;>p(||) <-> p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("<:=>", "selfassignd")
  lazy val assigndSelfAxiom = derivedAxiom("<:=> self assign",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=x_;>p(||) <-> p(||)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[:=] self assign")(1, 0::0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom ":= assign dual".
    *    <v:=t();>p(v) <-> [v:=t();]p(v)
    * End.
    * }}}
    *
    * @see [[assignDual2Axiom]]
    */
  @Axiom(":=D", "assignDual")
  lazy val assignDualAxiom = derivedAxiom(":= assign dual",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f();>p(x_) <-> [x_:=f();]p(x_)".asFormula)),
    useAt(assigndAxiom)(1, 0::Nil) &
      useAt("[:=] assign")(1, 1::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "[:=] assign equational".
    *    [v:=t();]p(v) <-> \forall v (v=t() -> p(v))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("[:=]==", "assignbequational", key = 0::Nil, recursor = Nil::(0::1::Nil)::Nil)
  lazy val assignbEquationalAxiom =
    derivedAxiom("[:=] assign equational",
      Sequent(IndexedSeq(), IndexedSeq("[x_:=f();]p(x_) <-> \\forall x_ (x_=f() -> p(x_))".asFormula)),
      useAt("[:=] assign")(1, 0::Nil) &
        commuteEquivR(1) &
        byUS(allSubstitute)
    )


  /**
    * {{{Axiom "[:=] assign update".
    *    [x:=t();]p(x) <-> [x:=t();]p(x)
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */
  @Axiom("[:=]", "assignbup", key = 0::Nil, recursor = (1::Nil)::Nil::Nil)
  lazy val assignbUpdate = derivedAxiom("[:=] assign update",
    Sequent(IndexedSeq(), IndexedSeq("[x_:=t_();]p_(x_) <-> [x_:=t_();]p_(x_)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<:=> assign update".
    *    <x:=t();>p(x) <-> <x:=t();>p(x)
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */
  @Axiom("<:=>", "assigndup", key = 0::Nil, recursor = (1::Nil)::Nil::Nil)
  lazy val assigndUpdate = derivedAxiom("<:=> assign update",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=t_();>p_(x_) <-> <x_:=t_();>p_(x_)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "[:=] vacuous assign".
    *    [v:=t();]p() <-> p()
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("V[:=]", "vacuousAssignb")
  lazy val vacuousAssignbAxiom = derivedAxiom("[:=] vacuous assign",
    Sequent(IndexedSeq(), IndexedSeq("[v_:=t_();]p_() <-> p_()".asFormula)),
    useAt("[:=] assign")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<:=> vacuous assign".
    *    <v:=t();>p() <-> p()
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("V<:=>", "vacuousAssignd")
  lazy val vacuousAssigndAxiom = derivedAxiom("<:=> vacuous assign",
    Sequent(IndexedSeq(), IndexedSeq("<v_:=t_();>p_() <-> p_()".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt(vacuousAssignbAxiom)(1, 0::0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "[':=] differential assign".
    *    [x_':=f();]p(x_') <-> p(f())
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val assignDAxiomb = DerivedAxiomProvableSig.axioms("[':=] differential assign")
  //@note the following derivation works if uniform renaming can mix BaseVariable with DifferentialSymbols.
  /*derivedAxiom("[':=] differential assign",
    Sequent(IndexedSeq(), IndexedSeq("[x_':=f();]p(x_') <-> p(f())".asFormula)),
    ProofRuleTactics.uniformRenaming(DifferentialSymbol(Variable("x_")), Variable("x_")) &
    byUS("[:=] assign")
//      useAt("[:=] assign")(1, 0::0::Nil) &
//      byUS(equivReflexiveAxiom)
  )*/

  /**
    * {{{Axiom "[':=] differential assign y".
    *    [y_':=f();]p(y_') <-> p(f())
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("[y':=]","[y':=]"), "Dassignby", "<span class=\"k4-axiom-key\">[y':=c]p(y')</span>↔p(c)", unifier = "full")
  lazy val assignDAxiomby = derivedAxiom("[':=] differential assign y",
    Sequent(IndexedSeq(), IndexedSeq("[y_':=f();]p(y_') <-> p(f())".asFormula)),
    byUS(assignDAxiomb))

  /**
    * {{{Axiom "<':=> differential assign".
    *    <v':=t();>p(v') <-> p(t())
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("<':=>","<':=>"), "Dassignd", key = 0::Nil, recursor = Nil::Nil)
  lazy val assignDAxiom = derivedAxiom("<':=> differential assign",
    Sequent(IndexedSeq(), IndexedSeq("<x_':=f();>p(x_') <-> p(f())".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[':=] differential assign", PosInExpr(0::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<:*> assign nondet".
    *    <x:=*;>p(x) <-> (\exists x p(x))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("<:*>", "randomd", key = 0::Nil, recursor = (0::Nil)::Nil::Nil)
  lazy val nondetassigndAxiom = derivedAxiom("<:*> assign nondet",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=*;>p_(||) <-> (\\exists x_ p_(||))".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[:*] assign nondet")(1, 0::0::Nil) &
      useAt("all dual", PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<?> test".
    *    <?q();>p() <-> (q() & p())
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("<?>", "testd", key = 0::Nil, recursor = (1::Nil)::Nil, unifier = "linear")
  lazy val testdAxiom = derivedAxiom("<?> test",
    Sequent(IndexedSeq(), IndexedSeq("<?q_();>p_() <-> (q_() & p_())".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[?] test")(1, 0::0::Nil) &
      prop
  )

  /* inverse testd axiom for chase */
  @Axiom("<?>i", "invtestd", key = 0::Nil, recursor = (1::Nil)::Nil, unifier = "linear")
  lazy val invTestdAxiom = derivedAxiom("<?> invtest",
    Sequent(IndexedSeq(), IndexedSeq("(q_() & p_()) <-> <?q_();>p_()".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt("[?] test")(1, 1::0::Nil) &
      prop
  )

  /* inverse testd axiom for chase */
  @Axiom("<?> combine", "testdcombine", key = 0::Nil, recursor = Nil::Nil, unifier = "linear")
  lazy val combineTestdAxiom =
    derivedAxiom("<?> combine",
      Sequent(IndexedSeq(), IndexedSeq("<?q_();><?p_();>r_() <-> <?q_()&p_();>r_()".asFormula)),
      useAt(testdAxiom)(1, 1::Nil) &
        useAt(testdAxiom)(1, 0::Nil) &
        useAt(testdAxiom)(1, 0::1::Nil) &
        prop
    )


  /**
    * {{{Axiom "<++> choice".
    *    <a;++b;>p(||) <-> (<a;>p(||) | <b;>p(||))
    * End.
    * }}}
    *
    * @todo first show de Morgan
    */
  @Axiom(("<∪>", "<++>"), "choiced", key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil , unifier = "linear")
  lazy val choicedAxiom = derivedAxiom("<++> choice",
    Sequent(IndexedSeq(), IndexedSeq("<a_;++b_;>p_(||) <-> (<a_;>p_(||) | <b_;>p_(||))".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[++] choice")(1, 0::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::Nil) &
      prop
  )

  /**
    * {{{Axiom "<;> compose".
    *    <a;b;>p(||) <-> <a;><b;>p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("<;>", "composed", key = 0::Nil, recursor = (1::Nil)::Nil::Nil, unifier = "linear")
  lazy val composedAxiom = derivedAxiom("<;> compose",
    Sequent(IndexedSeq(), IndexedSeq("<a_;b_;>p_(||) <-> <a_;><b_;>p_(||)".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[;] compose")(1, 0::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt(doubleNegationAxiom)(1, 1::0::1::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<*> iterate".
    *    <{a;}*>p(||) <-> (p(||) | <a;><{a;}*> p(||))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("<*>", "iterated", key = 0::Nil, recursor = (1::Nil)::Nil, unifier = "linear")
  lazy val iteratedAxiom = derivedAxiom("<*> iterate",
    Sequent(IndexedSeq(), IndexedSeq("<{a_;}*>p_(||) <-> (p_(||) | <a_;><{a_;}*> p_(||))".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[*] iterate")(1, 0::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::1::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::Nil) &
      useAt(notAnd)(1, 0::Nil) & //HilbertCalculus.stepAt(1, 0::Nil) &
      useAt(doubleNegationAxiom)(1, 1::1::0::1::Nil) &
      prop
  )

  /**
    * {{{Axiom "<*> approx".
    *    <a;>p(||) -> <{a;}*>p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("<*> approx", "loopApproxd", key = 1::Nil, recursor = Nil::Nil)
  lazy val loopApproxd = derivedAxiom("<*> approx",
    Sequent(IndexedSeq(), IndexedSeq("<a_;>p_(||) -> <{a_;}*>p_(||)".asFormula)),
    useAt(iteratedAxiom)(1, 1::Nil) &
      useAt(iteratedAxiom)(1, 1::1::1::Nil) &
      cut("<a_;>p_(||) -> <a_;>(p_(||) | <a_;><{a_;}*>p_(||))".asFormula) <(
        /* use */ prop,
        /* show */ hideR(1) & implyR('_) & mond & prop
        )
  )

  /**
    * {{{Axiom "[*] approx".
    *    [{a;}*]p(||) -> [a;]p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("[*] approx", "loopApproxb")
  lazy val loopApproxb = derivedAxiom("[*] approx",
    Sequent(IndexedSeq(), IndexedSeq("[{a_;}*]p_(||) -> [a_;]p_(||)".asFormula)),
    useAt("[*] iterate")(1, 0::Nil) &
      useAt("[*] iterate")(1, 0::1::1::Nil) &
      cut("[a_;](p_(||) & [a_;][{a_;}*]p_(||)) -> [a_;]p_(||)".asFormula) <(
        /* use */ prop,
        /* show */ hideR(1) & implyR('_) & monb & prop

        )
  )

  /**
    * {{{Axiom "II induction".
    *    [{a;}*](p(||)->[a;]p(||)) -> (p(||)->[{a;}*]p(||))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("II induction", "IIinduction")
  lazy val iiinduction = derivedAxiom("II induction",
    "==> [{a_{|^@|};}*](p_(||)->[a_{|^@|};]p_(||)) -> (p_(||)->[{a_{|^@|};}*]p_(||))".asSequent,
    useAt("I induction")(1, 1::1::Nil) & prop & done
  )


  /**
    * {{{Axiom "[*] merge".
    *    [{a;}*][{a;}*]p(||) <-> [{a;}*]p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("[*] merge", "loopMergeb")
  lazy val loopMergeb =
    derivedAxiom("[*] merge",
      "==> [{a_{|^@|};}*][{a_{|^@|};}*]p_(||) <-> [{a_{|^@|};}*]p_(||)".asSequent,
      equivR(1) <(
        useAt("[*] iterate")(-1) & prop & done,
        implyRi & useAt(iiinduction, PosInExpr(1::Nil))(1) & G(1) & useAt("[*] iterate")(1, 0::Nil) & prop & done
      )
    )

  /**
    * {{{Axiom "<*> merge".
    *    <{a;}*><{a;}*>p(||) <-> <{a;}*>p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("<*> merge", "loopMerged")
  lazy val loopMerged =
    derivedAxiom("<*> merge",
      "==> <{a_{|^@|};}*><{a_{|^@|};}*>p_(||) <-> <{a_{|^@|};}*>p_(||)".asSequent,
      equivR(1) <(
        useAt("<> diamond", PosInExpr(1::Nil))(1) & useAt(loopMergeb, PosInExpr(1::Nil))(1, 0::Nil) &
          useAt(boxAxiom, PosInExpr(1::Nil))(1, 0::1::Nil) & useAt("<> diamond")(1) &
          useAt(doubleNegationAxiom)(1, 1::1::Nil) & closeId & done,
        useAt(iteratedAxiom)(1) & prop & done
      )
    )

  /**
    * {{{Axiom "[**] iterate iterate".
    *    [{a;}*;{a;}*]p(||) <-> [{a;}*]p(||)
    * End.
    * }}}
    * @see Lemma 7.6 of textbook
    * @Derived
    */
  @Axiom("[**]", "iterateiterateb", unifier = "full")
  lazy val iterateiterateb = derivedAxiom("[**] iterate iterate",
    "==> [{a_{|^@|};}*;{a_{|^@|};}*]p_(||) <-> [{a_{|^@|};}*]p_(||)".asSequent,
    useAt("[;] compose")(1, 0::Nil) & by(loopMergeb)
  )

  /**
    * {{{Axiom "<**> iterate iterate".
    *    <{a;}*;{a;}*>p(||) <-> <{a;}*>p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("<**>", "iterateiterated", unifier = "full")
  lazy val iterateiterated = derivedAxiom("<**> iterate iterate",
    "==> <{a_{|^@|};}*;{a_{|^@|};}*>p_(||) <-> <{a_{|^@|};}*>p_(||)".asSequent,
    useAt(composedAxiom)(1, 0::Nil) & by(loopMerged)
  )

  /**
    * {{{Axiom "[*-] backiterate".
    *    [{a;}*]p(||) <-> p(||) & [{a;}*][{a;}]p(||)
    * End.
    * }}}
    * @see Lemma 7.5 in textbook
    * @Derived for programs
    */
  @Axiom("[*-]", "backiterateb", key = 0::Nil, recursor = (1::1::Nil)::Nil, unifier = "full")
  lazy val backiterateb =
    derivedAxiom("[*-] backiterate",
      "==> [{a_{|^@|};}*]p_(||) <-> p_(||) & [{a_{|^@|};}*][a_{|^@|};]p_(||)".asSequent,
      equivR(1) < (
        byUS(backiteratebnecc),
        by(backiteratebsuff)
      ))

  /**
    * {{{Axiom "[*-] backiterate sufficiency".
    *    [{a;}*]p(||) <- p(||) & [{a;}*][{a;}]p(||)
    * End.
    * }}}
    * @see Lemma 7.5 in textbook
    * @Derived for programs
    */
  @Axiom("[*-] backiterate sufficiency", "backiteratebsuff")
  lazy val backiteratebsuff = derivedAxiom("[*-] backiterate sufficiency",
    "p_(||) & [{a_{|^@|};}*][a_{|^@|};]p_(||) ==> [{a_{|^@|};}*]p_(||)".asSequent,
    andL(-1) & useAt(iiinduction, PosInExpr(1::1::Nil))(1) <(
      close(-1,1)
      ,
      hideL(-1) & byUS(boxMonotone) & implyR(1) & close(-1,1)
      )
  )

  /**
    * {{{Axiom "[*-] backiterate necessity".
    *    [{a;}*]p(||) -> p(||) & [{a;}*][{a;}]p(||)
    * End.
    * }}}
    * @see Figure 7.8 in textbook
    * @Derived for programs
    */
  @Axiom("[*-] backiterate necessity", "backiteratebnecc")
  lazy val backiteratebnecc =
    derivedAxiom("[*-] backiterate necessity",
      "[{b_{|^@|};}*]q_(||) ==> q_(||) & [{b_{|^@|};}*][b_{|^@|};]q_(||)".asSequent,
      andR(1) <(
        useAt("[*] iterate")(-1) & andL(-1) & close(-1,1)
        ,
        generalize("[{b_{|^@|};}*]q_(||)".asFormula)(1) <(
          useAt(iiinduction, PosInExpr(1::1::Nil))(1) <(
            close(-1,1)
            ,
            G(1) & useAt("[*] iterate")(1, 0::Nil) & prop
          )
          ,
          implyRi()(-1,1) & byUS(loopApproxb)
        )
      )
    )

  /**
    * {{{Axiom "Ieq induction".
    *    [{a;}*]p(||) <-> p(||) & [{a;}*](p(||)->[{a;}]p(||))
    * End.
    * }}}
    * @see Section 7.7.4 in textbook
    * @Derived for programs
    */
  // @TODO: Is this the same as Ieq induction?
  @Axiom(("I", "I"), "I", "<span class=\"k4-axiom-key\">[a*]P</span>↔P∧[a*](P→[a]P)", unifier = "linear")
  lazy val Ieq = derivedAxiom("I",
    "==> [{a_{|^@|};}*]p_(||) <-> p_(||) & [{a_{|^@|};}*](p_(||)->[a_{|^@|};]p_(||))".asSequent,
    equivR(1) <(
      andR(1) <(
        HilbertCalculus.iterateb(-1) & andL(-1) & close(-1,1)
        ,
        useAt(backiterateb)(-1) & andL(-1) & hideL(-1) & byUS(boxMonotone) & implyR(1) & close(-1,1)
        ),
      useAt(iiinduction, PosInExpr(1::1::Nil))(1) & OnAll(prop & done)
      )
  )


  //@todo this is somewhat indirect. Maybe it'd be better to represent derived axioms merely as Lemma and auto-wrap them within their ApplyRule[LookupLemma] tactics on demand.
  //private def useAt(lem: ApplyRule[LookupLemma]): PositionTactic = TactixLibrary.useAt(lem.rule.lemma.fact)

  /**
    * {{{Axiom "exists generalize".
    *    p(t()) -> (\exists x p(x))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("∃G","existsG"), "existsGeneralize")
  lazy val existsGeneralize =
    derivedAxiom("exists generalize",
      Sequent(IndexedSeq(), IndexedSeq("p_(f()) -> (\\exists x_ p_(x_))".asFormula)),
      useAt(existsDualAxiom, PosInExpr(1::Nil))(1, 1::Nil) &
        implyR(SuccPos(0)) &
        notR(SuccPos(0)) &
        useAt(allInstantiate, PosInExpr(0::Nil))(-2) &
        prop
    )

  @Axiom(("∃Gy","existsGy"), "existsGeneralizey")
  lazy val existsGeneralizey = derivedAxiom("exists generalize y",
    Sequent(IndexedSeq(), IndexedSeq("p_(f()) -> (\\exists y_ p_(y_))".asFormula)),
    useAt(existsDualAxiom, PosInExpr(1::Nil))(1, 1::Nil) &
      implyR(SuccPos(0)) &
      notR(SuccPos(0)) &
      useAt(allInstantiate, PosInExpr(0::Nil))(-2) &
      prop
  )

  /**
    * {{{Axiom "exists eliminate".
    *    p(||) -> (\exists x p(||))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("∃e","existse"), "existse", key = 1::Nil, recursor = Nil::Nil)
  lazy val existsEliminate = derivedAxiom("exists eliminate",
    Sequent(IndexedSeq(), IndexedSeq("p_(||) -> (\\exists x_ p_(||))".asFormula)),
    useAt(existsDualAxiom, PosInExpr(1::Nil))(1, 1::Nil) &
      implyR(1) &
      notR(1) &
      useAt("all eliminate", PosInExpr(0::Nil))(-2) &
      prop
    // also derives from existsDualAxiom & converseImply & doubleNegation & useAt("all eliminate")
  )

  /**
    * {{{Axiom "exists eliminate y"
    *    p(||) -> \exists y_ p(||)
    * End.
    * }}}
    */
  @Axiom(("∃ey","existsey"), "existsey")
  lazy val existsEliminatey = derivedAxiom("exists eliminate y",
    Sequent(IndexedSeq(), IndexedSeq("p_(||) -> (\\exists y_ p_(||))".asFormula)),
    useAt(existsDualAxiomy, PosInExpr(1::Nil))(1, 1::Nil) &
      implyR(1) &
      notR(1) &
      useAt(allEliminate_y, PosInExpr(0::Nil))(-2) &
      prop
    // also derives from existsDualAxiom & converseImply & doubleNegation & useAt(allEliminate_y)
  )

  /**
    * {{{Axiom "all then exists".
    *    (\forall x p(||)) -> (\exists x p(||))
    * End.
    * }}}
    *
    * @see [[forallThenExistsAxiom]]
    */
  @Axiom(("∀→∃","allThenExists"), "allThenExists")
  lazy val allThenExists = derivedFormula("all then exists",
    "(\\forall x_ p_(||)) -> (\\exists x_ p_(||))".asFormula,
    useAt(existsEliminate, PosInExpr(1::Nil))(1, 1::Nil) &
    useAt("all eliminate", PosInExpr(0::Nil))(1, 0::Nil) &
    implyR(1) & close(-1,1)
  )

  /**
    * {{{Axiom "all substitute".
    *    (\forall x (x=t() -> p(x))) <-> p(t())
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("∀S","allS"), "allSubstitute")
  lazy val allSubstitute =
    derivedAxiom("all substitute",
      Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ (x_=t_() -> p_(x_))) <-> p_(t_())".asFormula)),
      equivR(SuccPos(0)) <(
        /* equiv left */ allL(Variable("x_"), "t_()".asTerm)(-1) & implyL(-1) <(cohide(2) & byUS(equalReflex), close),
        /* equiv right */ allR(1) & implyR(1) & eqL2R(-2)(1) & close
      )
    )

  /**
    * {{{Axiom "vacuous exists quantifier".
    *    (\exists x p()) <-> p()
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("V∃","existsV"), "existsV", key = 0::Nil, recursor = Nil::Nil)
  lazy val vacuousExistsAxiom = derivedAxiom("vacuous exists quantifier",
    Sequent(IndexedSeq(), IndexedSeq("(\\exists x_ p_()) <-> p_()".asFormula)),
    useAt(existsDualAxiom, PosInExpr(1::Nil))(1, 0::Nil) &
      useAt(vacuousAllAxiom)(1, 0::0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "partial vacuous exists quantifier".
    *    (\exists x p(x) & q()) <-> (\exists x p(x)) & q()
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("pV∃","pexistsV"), "pexistsV")
  lazy val partialVacuousExistsAxiom =
    derivedAxiom("partial vacuous exists quantifier",
      Sequent(IndexedSeq(), IndexedSeq("\\exists x_ (p_(x_) & q_()) <-> \\exists x_ p_(x_) & q_()".asFormula)),
      equivR(1) <(
        existsL(-1) & andR(1) <(existsR("x_".asVariable)(1) & prop & done, prop & done),
        andL('L) & existsL(-1) & existsR("x_".asVariable)(1) & prop & done
      )
    )

  /**
    * {{{Axiom "V[:*] vacuous assign nondet".
    *    [x:=*;]p() <-> p()
    * End.
    * @todo reorient
    * @Derived
    * */
  @Axiom("V[:*]", "vacuousBoxAssignNondet")
  lazy val vacuousBoxAssignNondetAxiom =
    derivedAxiom("V[:*] vacuous assign nondet",
      Sequent(IndexedSeq(), IndexedSeq("([x_:=*;]p_()) <-> p_()".asFormula)),
      useAt("[:*] assign nondet")(1, 0::Nil) &
        useAt(vacuousAllAxiom)(1, 0::Nil) &
        byUS(equivReflexiveAxiom)
    )

  /**
    * {{{Axiom "V<:*> vacuous assign nondet".
    *    <x:=*;>p() <-> p()
    * End.
    * }}}
    *
    * @todo reorient
    * @Derived
    */
  @Axiom("V<:*>", "vacuousDiamondAssignNondet")
  lazy val vacuousDiamondAssignNondetAxiom = derivedAxiom("V<:*> vacuous assign nondet",
    Sequent(IndexedSeq(), IndexedSeq("(<x_:=*;>p_()) <-> p_()".asFormula)),
    useAt(nondetassigndAxiom)(1, 0::Nil) &
      useAt(vacuousExistsAxiom)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "Domain Constraint Conjunction Reordering".
    *    [{c & (H(||) & q(||))}]p(||) <-> [{c & (q(||) & H(||))}]p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("{∧}C","{&}C"), "domainCommute")
  lazy val domainCommute = derivedAxiom("Domain Constraint Conjunction Reordering",
    Sequent(IndexedSeq(), IndexedSeq("[{c_ & (H_(||) & q_(||))}]p_(||) <-> [{c_ & (q_(||) & H_(||))}]p_(||)".asFormula)),
    useAt(andCommute)(1, 0::0::1::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "[] post weaken".
    *   [a;]p(||)  ->  [a;](q(||)->p(||))
    * End.
    * }}}
    *
    * @Derived from M (or also from K)
    */
  @Axiom("[]PW", "postWeaken", key = 1::Nil, recursor = Nil::Nil)
  lazy val postconditionWeaken = derivedAxiom("[] post weaken",
    Sequent(IndexedSeq(), IndexedSeq("([a_;]p_(||))  ->  [a_;](q_(||)->p_(||))".asFormula)),
    implyR(1) & monb & prop
  )

  /**
    * {{{Axiom "& commute".
    *    (p() & q()) <-> (q() & p())
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("∧C","&C"), "andCommute", unifier = "linear")
  lazy val andCommute = derivedAxiom("& commute", Sequent(IndexedSeq(), IndexedSeq("(p_() & q_()) <-> (q_() & p_())".asFormula)), prop)

  /**
    * {{{Axiom "& associative".
    *    ((p() & q()) & r()) <-> (p() & (q() & r()))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("∧A","&A"), "andAssoc", unifier = "linear")
  lazy val andAssoc = derivedAxiom("& associative", Sequent(IndexedSeq(), IndexedSeq("((p_() & q_()) & r_()) <-> (p_() & (q_() & r_()))".asFormula)), prop)

  /**
    * {{{Axiom "& reflexive".
    *    p() & p() <-> p()
    * End.
    * }}}
    */
  @Axiom(("∧R","&R"), "andReflexive", unifier = "full")
  lazy val andReflexive = derivedAxiom("& reflexive", Sequent(IndexedSeq(), IndexedSeq("p_() & p_() <-> p_()".asFormula)), prop)

  /**
    * {{{Axiom "<-> true".
    *    (p() <-> true) <-> p()
    * End.
    * }}}
    */
  @Axiom(("↔true","<-> true"), "equivTrue", unifier = "linear")
  lazy val equivTrue = derivedAxiom("<-> true", Sequent(IndexedSeq(), IndexedSeq("(p() <-> true) <-> p()".asFormula)), prop)

  /**
    * {{{Axiom "-> self".
    *    (p() -> p()) <-> true
    * End.
    * }}}
    */
  @Axiom(("→self","-> self"), "implySelf")
  lazy val implySelf = derivedAxiom("-> self", Sequent(IndexedSeq(), IndexedSeq("(p_() -> p_()) <-> true".asFormula)), prop)

  /**
    * {{{Axiom "-> converse".
    *    (p() -> q()) <-> (!q() -> !p())
    * End.
    * }}}
    */
  @Axiom(("→conv","-> conv"), "converseImply")
  lazy val converseImply = derivedAxiom("-> converse", Sequent(IndexedSeq(), IndexedSeq("(p_() -> q_()) <-> (!q_() -> !p_())".asFormula)), prop)

  /**
    * {{{Axiom "!& deMorgan".
    *    (!(p() & q())) <-> ((!p()) | (!q()))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("¬∧", "!&"), codeName = "notAnd", formula = "<span class=\"k4-axiom-key\">¬(p∧q)</span>↔(¬p|¬q)", unifier = "linear", key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  lazy val notAnd = derivedAxiom("!& deMorgan", Sequent(IndexedSeq(), IndexedSeq("(!(p_() & q_())) <-> ((!p_()) | (!q_()))".asFormula)), prop)

  /**
    * {{{Axiom "!| deMorgan".
    *    (!(p() | q())) <-> ((!p()) & (!q()))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("¬∨","!|"), codeName = "notOr", formula = "<span class=\"k4-axiom-key\">(¬(p|q))</span>↔(¬p∧¬q)", unifier = "linear", key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  lazy val notOr = derivedAxiom("!| deMorgan", Sequent(IndexedSeq(), IndexedSeq("(!(p_() | q_())) <-> ((!p_()) & (!q_()))".asFormula)), prop)

  /**
    * {{{Axiom "!-> deMorgan".
    *    (!(p() -> q())) <-> ((p()) & (!q()))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("¬→","!->"), "notImply", formula = "<span class=\"k4-axiom-key\">¬(p->q)</span>↔(p∧¬q)", unifier = "linear",
    key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  lazy val notImply = derivedAxiom("!-> deMorgan", Sequent(IndexedSeq(), IndexedSeq("(!(p_() -> q_())) <-> ((p_()) & (!q_()))".asFormula)), prop)

  /**
    * {{{Axiom "!<-> deMorgan".
    *    (!(p() <-> q())) <-> (((p()) & (!q())) | ((!p()) & (q())))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("¬↔", "!<->"), codeName = "notEquiv", formula = "<span class=\"k4-axiom-key\">¬(p↔q)</span>↔(p∧¬q)| (¬p∧q)", unifier = "linear"
  , key = 0::Nil, recursor = (0::0::Nil)::(0::1::Nil)::(1::0::Nil)::(1::1::Nil)::Nil)
  lazy val notEquiv = derivedAxiom("!<-> deMorgan", Sequent(IndexedSeq(), IndexedSeq("(!(p_() <-> q_())) <-> (((p_()) & (!q_())) | ((!p_()) & (q_())))".asFormula)), prop)

  /**
    * {{{Axiom "-> expand".
    *    (p() -> q()) <-> ((!p()) | q())
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("→E","->E"), codeName = "implyExpand", unifier = "linear", key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  lazy val implyExpand = derivedAxiom("-> expand", Sequent(IndexedSeq(), IndexedSeq("(p_() -> q_()) <-> ((!p_()) | q_())".asFormula)), prop)

  /**
    * {{{Axiom "PC1".
    *    p()&q() -> p()
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, PC1
    */
  @Axiom("PC1", "PC1", unifier = "full")
  lazy val PC1 = derivedAxiom("PC1", Sequent(IndexedSeq(), IndexedSeq("p_()&q_() -> p_()".asFormula)), prop)

  /**
    * {{{Axiom "PC2".
    *    p()&q() -> q()
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, PC2
    */
  @Axiom("PC2", "PC2", unifier = "full")
  lazy val PC2 = derivedAxiom("PC2", Sequent(IndexedSeq(), IndexedSeq("p_()&q_() -> q_()".asFormula)), prop)

  /**
    * {{{Axiom "PC3".
    *    p()&q() -> ((p()->r())->(p()->q()&r())) <-> true
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, PC3
    */
  @Axiom("PC3", "PC3", unifier = "full")
  lazy val PC3 = derivedAxiom("PC3", Sequent(IndexedSeq(), IndexedSeq("p_()&q_() -> ((p_()->r_())->(p_()->q_()&r_())) <-> true".asFormula)), prop)

  /**
    * {{{Axiom "PC9".
    *    p() -> p() | q()
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, PC9
    */
  @Axiom("PC9", "PC9", unifier = "full")
  lazy val PC9 = derivedAxiom("PC9", Sequent(IndexedSeq(), IndexedSeq("p_() -> p_() | q_()".asFormula)), prop)

  /**
    * {{{Axiom "PC10".
    *    q() -> p() | q()
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, PC10
    */
  @Axiom("PC10", "PC10", unifier = "full")
  lazy val PC10 = derivedAxiom("PC10", Sequent(IndexedSeq(), IndexedSeq("q_() -> p_() | q_()".asFormula)), prop)

  /**
    * {{{Axiom "-> tautology".
    *    (p() -> (q() -> p()&q())) <-> true
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("→taut","->taut"), "implyTautology", unifier = "full")
  lazy val implyTautology = derivedAxiom("-> tautology", Sequent(IndexedSeq(), IndexedSeq("(p_() -> (q_() -> p_()&q_())) <-> true".asFormula)), prop)

  /**
    * {{{Axiom "->' derive imply".
    *    (p(||) -> q(||))' <-> (!p(||) | q(||))'
    * End.
    * }}}
    *
    * @Derived by CE
    */
  @Axiom(("→'","->'"), "Dimply", formula = "<span class=\"k4-axiom-key\">(P→Q)'</span>↔(¬P∨Q)'", unifier = "linear")
  lazy val Dimply = derivedAxiom("->' derive imply",
    Sequent(IndexedSeq(), IndexedSeq("(p_(||) -> q_(||))' <-> (!p_(||) | q_(||))'".asFormula)),
    useAt(implyExpand)(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "\forall->\exists".
    *    (\forall x p(x)) -> (\exists x p(x))
    * End.
    * }}}
    *
    * @see [[allThenExists]]
    */
  @Axiom(("∀→∃","all->exists"), "forallThenExists")
  lazy val forallThenExistsAxiom = derivedAxiom("\\forall->\\exists",
    Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ p_(x_)) -> (\\exists x_ p_(x_))".asFormula)),
    implyR(1) &
      useAt(existsGeneralize, PosInExpr(1::Nil))(1) &
      useAt(allInstantiate)(-1) &
      closeId
  )

  /**
    * {{{Axiom "->true".
    *    (p()->true) <-> true
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("→⊤","->T"), "implyTrue", formula = "<span class=\"k4-axiom-key\">(p→⊤)</span>↔⊤", unifier = "linear")
  lazy val impliesTrue = derivedAxiom("->true", Sequent(IndexedSeq(), IndexedSeq("(p_()->true) <-> true".asFormula)), prop)

  /**
    * {{{Axiom "true->".
    *    (true->p()) <-> p()
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom(("⊤→", "T->"), "trueImply", formula = "<span class=\"k4-axiom-key\">(⊤→p)</span>↔p", unifier = "linear")
  lazy val trueImplies = derivedAxiom("true->", Sequent(IndexedSeq(), IndexedSeq("(true->p_()) <-> p_()".asFormula)), prop)

  /**
   * {{{Axiom "&true".
   *    (p()&true) <-> p()
   * End.
   * }}}
    *
    * @Derived
   */
  @Axiom(("∧⊤","&T"), "andTrue", formula = "<span class=\"k4-axiom-key\">(p∧⊤)</span>↔p", unifier = "linear")
  lazy val andTrue = derivedAxiom("&true", Sequent(IndexedSeq(), IndexedSeq("(p_()&true) <-> p_()".asFormula)), prop)

  /* inverse andtrue axiom for chase */
  @Axiom("&true inv", "andTrueInv", key = 0::Nil, recursor = Nil::Nil)
  lazy val invAndTrue = derivedAxiom("&true inv", Sequent(IndexedSeq(), IndexedSeq("p_() <-> (p_()&true)".asFormula)), prop)

  /**
   * {{{Axiom "true&".
   *    (true&p()) <-> p()
   * End.
   * }}}
    *
    * @Derived
   */
  @Axiom(("⊤∧","T&"), "trueAnd", formula = "<span class=\"k4-axiom-key\">(⊤∧p)</span>↔p", unifier = "linear")
  lazy val trueAnd = derivedAxiom("true&", Sequent(IndexedSeq(), IndexedSeq("(true&p_()) <-> p_()".asFormula)), prop)

  /**
   * {{{Axiom "0*".
   *    (0*f()) = 0
   * End.
   * }}}
    *
    * @Derived
   */
  @Axiom("0*", "zeroTimes", unifier = "linear")
  lazy val zeroTimes = derivedAxiom("0*", Sequent(IndexedSeq(), IndexedSeq("(0*f_()) = 0".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (0*x = 0)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "*0".
    *    (f()*0) = 0
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("*0", "timesZero", unifier = "linear")
  lazy val timesZero = derivedAxiom("*0", Sequent(IndexedSeq(), IndexedSeq("(f_()*0) = 0".asFormula)),
    if (false) useAt(timesCommutative)(1, 0::Nil) & byUS(zeroTimes)
    else allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (x*0 = 0)".asFormula, TactixLibrary.RCF))
  )

  /**
   * {{{Axiom "0+".
   *    (0+f()) = f()
   * End.
   * }}}
    *
    * @Derived
   */
  @Axiom("0+", "zeroPlus", unifier = "linear")
  lazy val zeroPlus = derivedAxiom("0+", Sequent(IndexedSeq(), IndexedSeq("(0+f_()) = f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (0+x = x)".asFormula, TactixLibrary.RCF)))

  /**
    * {{{Axiom "+0".
    *    (f()+0) = f()
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("+0", "plusZero", unifier = "linear")
  lazy val plusZero = derivedAxiom("+0", Sequent(IndexedSeq(), IndexedSeq("(f_()+0) = f_()".asFormula)),
    if (false) useAt(plusCommutative)(1, 0::Nil) & byUS(zeroPlus)
    else allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (x+0 = x)".asFormula, TactixLibrary.RCF))
  )

  // differential equations

  /**
    * {{{Axiom "DW differential weakening".
    *    [{c&q(||)}]p(||) <-> ([{c&q(||)}](q(||)->p(||)))
    *    /* [x'=f(x)&q(x);]p(x) <-> ([x'=f(x)&q(x);](q(x)->p(x))) THEORY */
    * End.
    * }}}
    *
    * @see footnote 3 in "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, volume 9195 of LNCS, pages 467-481. Springer, 2015. arXiv 1503.01981, 2015."
    */
  @Axiom("DW", "DW", formula = "[x'=f(x)&Q]P↔[x'=f(x)&Q](Q→P)", unifier =  "linear", key = (0::Nil), recursor = Nil)
  lazy val DWeakening =
    derivedAxiom("DW differential weakening",
    Sequent(IndexedSeq(), IndexedSeq("[{c_&q_(||)}]p_(||) <-> ([{c_&q_(||)}](q_(||)->p_(||)))".asFormula)),
    equivR(1) <(
      /* equiv left */
      cut("[{c_&q_(||)}](p_(||)->(q_(||)->p_(||)))".asFormula) <(
        /* use */ useAt("K modal modus ponens", PosInExpr(0::Nil))(-2) & implyL(-2) <(close, close),
        /* show */ G(2) & prop
        ),
      /* equiv right */
      useAt("K modal modus ponens", PosInExpr(0::Nil))(-1) & implyL(-1) <(cohide(2) & byUS("DW base"), close)
      )
  )

  /**
    * {{{Axiom "DW differential weakening and".
    *    [{c&q(||)}]p(||) -> ([{c&q(||)}](q(||)&p(||)))
    * End.
    * }}}
    */
  @Axiom("DW∧", "DWeakenAnd", formula = "[x'=f(x)&Q]P→[x'=f(x)&Q](Q∧P)")
  lazy val DWeakeningAnd = derivedAxiom("DW differential weakening and",
    Sequent(IndexedSeq(), IndexedSeq("[{c_&q_(||)}]p_(||) -> ([{c_&q_(||)}](q_(||)&p_(||)))".asFormula)),
    implyR(1) & cut("[{c_&q_(||)}](q_(||)->(p_(||)->(q_(||)&p_(||))))".asFormula) <(
      /* use */ useAt("K modal modus ponens", PosInExpr(0::Nil))('Llast) & implyL('Llast) <(
        cohide('Rlast) & byUS("DW base") & done,
        useAt("K modal modus ponens", PosInExpr(0::Nil))('Llast) & implyL('Llast) <(close, close)),
      /* show */ G('Rlast) & prop
      )
  )

  /**
    * {{{Axiom "DR differential refine".
    *    ([{c&q(||)}]p(||) <- [{c&r(||)}]p(||)) <- [{c&q(||)}]r(||)
    * End.
    *
    * @Derived
    * }}}
    */
  @Axiom("DR", "DR", formula = "(<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]P</span>←[{x'=f(x)&R}]P)←[{x'=f(x)&Q}]R",
  unifier = "linear", inputs = "R:formula")
  lazy val DiffRefine = derivedAxiom("DR differential refine",
    Sequent(IndexedSeq(),IndexedSeq("([{c&q(||)}]p(||) <- [{c&r(||)}]p(||)) <- [{c&q(||)}]r(||)".asFormula)),
    implyR(1) &
      useAt("DMP differential modus ponens", PosInExpr(1::Nil))(1) &
      useAt(DWeakening, PosInExpr(1::Nil))(1) & closeId
  )

  /**
    * {{{Axiom "DR<> diamond differential refine".
    *    (<{c&q(||)}>p(||) <- <{c&r(||)}>p(||)) <- [{c&r(||)}]q(||)
    * End.
    *
    * @Derived
    * }}}
    */
  @Axiom("DRd","DRd", formula = "(<span class=\"k4-axiom-key\"><{x'=f(x)&Q}>P</span>←<{x'=f(x)&R}>P)←[{x'=f(x)&R}]Q",
    inputs = "R:formula", unifier = "linear")
  lazy val DiffRefineDiamond = derivedAxiom("DR<> differential refine",
    Sequent(IndexedSeq(),IndexedSeq("(<{c&q(||)}>p(||) <- <{c&r(||)}>p(||)) <- [{c&r(||)}]q(||)".asFormula)),
    implyR(1) & implyR(1) &
      useAt("<> diamond", PosInExpr(1::Nil))(1) &
      useAt("<> diamond", PosInExpr(1::Nil))(-2) & notL(-2) & notR(1) &
      implyRi()(AntePos(1), SuccPos(0)) & implyRi &
      byUS(DiffRefine)
  )

  /**
    * {{{Axiom "DC differential cut".
    *    ([{c&q(||)}]p(||) <-> [{c&(q(||)&r(||))}]p(||)) <- [{c&q(||)}]r(||)
    * End.
    *
    * @Derived
    * }}}
    */
  @Axiom("DC", "DC", formula = "(<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]P</span>↔[{x'=f(x)&Q∧R}]P)←[{x'=f(x)&Q}]R",
    unifier = "linear", inputs = "R:formula", key = (1::0::Nil), recursor = Nil::Nil)
  lazy val DiffCut = derivedAxiom("DC differential cut",
    Sequent(IndexedSeq(),IndexedSeq("([{c&q(||)}]p(||) <-> [{c&(q(||)&r(||))}]p(||)) <- [{c&q(||)}]r(||)".asFormula)),
    implyR(1) & equivR(1) <(
      implyRi()(AntePos(1), SuccPos(0)) &
        useAt(DiffRefine, PosInExpr(1::Nil))(1) &
        useAt(DWeakening, PosInExpr(0::Nil))(1) & G(1) & prop
      ,
      useAt(DWeakeningAnd, PosInExpr(0::Nil))(-1) &
        implyRi()(AntePos(1), SuccPos(0)) & implyRi & byUS(DiffRefine)
    )
  )

  /**
    * {{{Axiom "DI differential invariance".
    *  ([{c&q(||)}]p(||) <-> [?q(||);]p(||)) <- (q(||) -> [{c&q(||)}]((p(||))'))
    *  //([x'=f(x)&q(x);]p(x) <-> [?q(x);]p(x)) <- (q(x) -> [x'=f(x)&q(x);]((p(x))')) THEORY
    * End.
    * }}}
    *
    * @Derived
    */
  private lazy val DIinvarianceF = "([{c&q(||)}]p(||) <-> [?q(||);]p(||)) <- (q(||) -> [{c&q(||)}]((p(||))'))".asFormula
  lazy val DIinvariance = DerivedAxiomProvableSig.axioms("DI differential invariance") /*derivedAxiom("DI differential invariance",
    Sequent(IndexedSeq(), IndexedSeq(DIinvarianceF)),
    implyR(1) & equivR(1) <(
      testb(1) &
        useAt("DX differential skip")(-2) &
        close
      ,
      testb(-2) &
        useAt("DI differential invariant")(1) &
        prop & onAll(close)
    )
  )*/

  /**
    * {{{Axiom "DI differential invariant".
    *    [{c&q(||)}]p(||) <- (q(||)-> (p(||) & [{c&q(||)}]((p(||))')))
    *    // [x'=f(x)&q(x);]p(x) <- (q(x) -> (p(x) & [x'=f(x)&q(x);]((p(x))'))) THEORY
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("DI", "DI", formula = "<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]P</span>←(Q→P∧[{x'=f(x)&Q}](P)')"
    , unifier = "linear", key = (1::Nil), recursor = (1::1::Nil)::Nil)
  lazy val DIinvariant = derivedAxiom("DI differential invariant",
    Sequent(IndexedSeq(), IndexedSeq("[{c&q(||)}]p(||) <- (q(||)-> (p(||) & [{c&q(||)}]((p(||))')))".asFormula)),
    implyR(1) & useAt(implyDistAndAxiom, PosInExpr(0::Nil))(-1) & andL(-1) &
      useAt("[?] test", PosInExpr(1::Nil))(-1) &
      cut(DIinvarianceF) <(
        prop & onAll(close)
        ,
        cohide(2) & by(DIinvariance)
        )
  )

  /**
    * {{{Axiom "DIo open differential invariance <".
    *    ([{c&q(||)}]f(||)<g(||) <-> [?q(||);]f(||)<g(||)) <- (q(||) -> [{c&q(||)}](f(||)<g(||) -> (f(||)<g(||))'))
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("DIo <", "DIoless", formula = "(<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]g(x)<h(x)</span>↔[?Q]g(x)<h(x))←(Q→[{x'=f(x)&Q}](g(x)<h(x)→(g(x)<h(x))'))"
    , unifier = "linear")
  lazy val DIOpeninvariantLess =
    derivedAxiom("DIo open differential invariance <",
      Sequent(IndexedSeq(), IndexedSeq("([{c&q(||)}]f(||)<g(||) <-> [?q(||);]f(||)<g(||)) <- (q(||) -> [{c&q(||)}](f(||)<g(||) -> (f(||)<g(||))'))".asFormula)),
      useAt(flipLess)(1, 1::0::1::Nil) &
        useAt(flipLess)(1, 1::1::1::Nil) &
        useAt(flipLess)(1, 0::1::1::0::Nil) &
        HilbertCalculus.Derive.Dless(1, 0::1::1::1::Nil) &
        useAt(flipLessEqual)(1, 0::1::1::1::Nil) &
        useExpansionAt(">' derive >")(1, 0::1::1::1::Nil) &
        byUS("DIo open differential invariance >")
    )

//  /**
//    * {{{Axiom "DV differential variant <=".
//    *    <{c&true}>f(||)<=g(||) <- \exists e_ (e_>0 & [{c&true}](f(||)>=g(||) -> f(||)'<=g(||)'-e_))
//    * End.
//    * }}}
//    *
//    * @Derived
//    */
//  lazy val DVLessEqual = derivedAxiom("DV differential variant <=",
//    Sequent(IndexedSeq(), IndexedSeq("<{c&true}>f(||)<=g(||) <- \\exists e_ (e_>0 & [{c&true}](f(||)>=g(||) -> f(||)'<=g(||)'-e_))".asFormula)),
//    useAt(flipLessEqual.fact)(1, 1::1::Nil) &
//      useAt(flipGreaterEqual.fact)(1, 0::0::1::1:: 0::Nil) &
//      useAt(flipLessEqual.fact)(1, 0::0::1::1:: 1::Nil) &
//      // transform g(||)'+e_<=f(||)' to g(||)'<=f(||)'-e_
//      useAt(TactixLibrary.proveBy("s()-r()>=t() <-> s()>=t()+r()".asFormula, QE & done), PosInExpr(0::Nil))(1, 0::0::1::1:: 1::Nil) &
//      byUS("DV differential variant >=")
//  )

  /**
    * {{{Axiom "DX diamond differential skip".
    *    <{c&q(||)}>p(||) <- q(||)&p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("DX", "Dskipd", unifier = "linear", key = (1::Nil), recursor = (1::Nil)::Nil)
  lazy val Dskipd = derivedAxiom("DX diamond differential skip",
    Sequent(IndexedSeq(), IndexedSeq("<{c&q(||)}>p(||) <- q(||)&p(||)".asFormula)),
    useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::Nil) &
      useAt(notAnd)(1, 0::0::Nil) &
      useAt(implyExpand, PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt("DX differential skip", PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt("<> diamond")(1, 0::Nil) & implyR(1) & close
  )

  /**
    * {{{Axiom "DS differential equation solution".
    *    [{x'=c()}]p(x) <-> \forall t (t>=0 -> [x:=x+(c()*t);]p(x))
    * End.
    * }}}
    *
    * @Derived
    * @TODO postcondition formulation is weaker than that of DS&
    */
  @Axiom("DS", "DSnodomain", unifier = "linear")
  lazy val DSnodomain =
    derivedAxiom("DS differential equation solution",
      Sequent(IndexedSeq(), IndexedSeq("[{x_'=c_()}]p_(x_) <-> \\forall t_ (t_>=0 -> [x_:=x_+(c_()*t_);]p_(x_))".asFormula)),
      useAt("DS& differential equation solution")(1, 0::Nil) &
        useAt(impliesTrue)(1, 0::0::1::0::0::Nil) &
        useAt(vacuousAllAxiom)(1, 0::0::1::0::Nil) &
        useAt(trueImplies)(1, 0::0::1::Nil) &
        byUS(equivReflexiveAxiom)
    )


  /**
    * {{{Axiom "Dsol differential equation solution".
    *    <{x'=c()}>p(x) <-> \exists t (t>=0 & <x:=x+(c()*t);>p(x))
    * End.
    * }}}
    *
    * @Derived
    * @TODO postcondition formulation is weaker than that of DS&
    */
  @Axiom("DS", "DSdnodomain", unifier = "linear")
  lazy val DSdnodomain =
    derivedAxiom("Dsol differential equation solution",
    Sequent(IndexedSeq(), IndexedSeq("<{x_'=c_()}>p_(x_) <-> \\exists t_ (t_>=0 & <x_:=x_+(c_()*t_);>p_(x_))".asFormula)),
    useAt(DSddomain)(1, 0::Nil) &
      useAt(impliesTrue)(1, 0::0::1::0::0::Nil) &
      useAt(vacuousAllAxiom)(1, 0::0::1::0::Nil) &
      useAt(trueAnd)(1, 0::0::1::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "Dsol& differential equation solution".
    *    <{x'=c()&q(x)}>p(||) <-> \exists t (t>=0 & ((\forall s ((0<=s&s<=t) -> q(x+(c()*s)))) & <x:=x+(c()*t);>p(||)))
    * End.
    * }}}
    */
  @Axiom("DS&", "DSddomain", unifier = "linear")
  lazy val DSddomain = derivedAxiom("Dsol& differential equation solution",
    Sequent(IndexedSeq(), IndexedSeq("<{x_'=c()&q(x_)}>p(|x_'|) <-> \\exists t_ (t_>=0 & ((\\forall s_ ((0<=s_&s_<=t_) -> q(x_+(c()*s_)))) & <x_:=x_+(c()*t_);>p(|x_'|)))".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("DS& differential equation solution")(1, 0::0::Nil) &
      useAt(allDual_time, PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom)(1, 0::Nil) &
      useAt(notImply)(1, 0::0::Nil) &
      useAt(notImply)(1, 0::0::1::Nil) &
      useAt("<> diamond")(1, 0::0::1::1::Nil) &
      //useAt("& associative", PosInExpr(1::Nil))(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  //  lazy val existsDualAxiom: LookupLemma = derivedAxiom("exists dual",
  //    Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("\\exists x q(x) <-> !(\\forall x (!q(x)))".asFormula)))
  //      (CutRight("\\exists x q(x) <-> !!(\\exists x (!!q(x)))".asFormula, SuccPos(0)), 0)
  //      // right branch
  //      (EquivifyRight(SuccPos(0)), 1)
  //      (AxiomaticRule("CE congruence", USubst(
  //        SubstitutionPair(PredicationalOf(context, DotFormula), "\\exists x q(x) <-> !⎵".asFormula) ::
  //          SubstitutionPair(pany, "!\\exists x !!q(x)".asFormula) ::
  //          SubstitutionPair(qany, "\\forall x !q(x)".asFormula) :: Nil
  //      )), 1)
  //      (CommuteEquivRight(SuccPos(0)), 1)
  //      (Axiom("all dual"), 1)
  //      (Close(AntePos(0),SuccPos(0)), 1)
  //  )


  /**
    * {{{Axiom "DG differential pre-ghost".
    *    [{c{|y_|}&q(|y_|)}]p(|y_|) <-> \exists y_ [{y_'=(a(|y_|)*y_)+b(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)
    *    // [x'=f(x)&q(x);]p(x) <-> \exists y [{y'=(a(x)*y)+b(x), x'=f(x))&q(x)}]p(x) THEORY
    * End.
    * }}}
    * Pre Differential Auxiliary / Differential Ghost -- not strictly necessary but saves a lot of reordering work.
    */
  @Axiom("DG", "DGpreghost")
  lazy val DGpreghost = derivedAxiom("DG differential pre-ghost",
    Sequent(IndexedSeq(), IndexedSeq("[{c{|y_|}&q(|y_|)}]p(|y_|) <-> \\exists y_ [{y_'=(a(|y_|)*y_)+b(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)".asFormula)),
    useAt("DG differential ghost")(1, 0::Nil) &
      useAt(", commute")(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  // diamond differential axioms

  /**
    * {{{Axiom "DGd diamond differential ghost".
    *    <{c{|y_|}&q(|y_|)}>p(|y_|) <-> \forall y_ <{c{|y_|},y_'=(a(|y_|)*y_)+b(|y_|)&q(|y_|)}>p(|y_|)
    *    // <x'=f(x)&q(x);>p(x) <-> \forall y <{x'=f(x),y'=(a(x)*y)+b(x))&q(x)}>p(x) THEORY
    * End.
    * }}}
    */
  @Axiom("DGd", "DGd")
  lazy val DGddifferentialghost = derivedAxiom("DGd diamond differential ghost",
    Sequent(IndexedSeq(), IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\forall y_ <{c{|y_|},y_'=(a(|y_|)*y_)+b(|y_|)&q(|y_|)}>p(|y_|)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("DG differential ghost")(1, 0::0::Nil) &
      useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::0::0::Nil) &
      useAt(allDual_y, PosInExpr(0::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(0::Nil))(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )


  /**
    * {{{Axiom "DGd diamond inverse differential ghost implicational".
    *    <{c{|y_|}&q(|y_|)}>p(|y_|)  ->  \exists y_ <{y_'=a(||),c{|y_|}&q(|y_|)}>p(|y_|)
    * End.
    * }}}
    */
  @Axiom("DGdi", "DGdi")
  lazy val DGdinversedifferentialghostimplicational = derivedAxiom("DGd diamond inverse differential ghost implicational",
    Sequent(IndexedSeq(), IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|)  <-  \\exists y_ <{y_'=a(||),c{|y_|}&q(|y_|)}>p(|y_|)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::0::1::Nil) &
      useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::Nil) &
      useAt(allDual_y)(1, 0::0::Nil) &
      useAt(boxAxiom)(1, 0::0::0::Nil) &
      useAt(converseImply, PosInExpr(1::Nil))(1) &
      byUS("DG inverse differential ghost implicational")
  )

  /**
    * {{{Axiom "DGCd diamond differential ghost const".
    *    <{c{|y_|}&q(|y_|)}>p(|y_|) <-> \forall y_ <{c{|y_|},y_'=b(|y_|)&q(|y_|)}>p(|y_|)
    * End.
    * }}}
    */
  @Axiom("DG", "DGCd", formula = "<span class=\"k4-axiom-key\">[{x'=f(x)&Q}]P</span>↔∃y [{x'=f(x),y'=g()&Q}]P")
  lazy val DGCddifferentialghostconst =
    derivedAxiom("DGd diamond differential ghost constant",
      Sequent(IndexedSeq(), IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\forall y_ <{c{|y_|},y_'=b(|y_|)&q(|y_|)}>p(|y_|)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
        useAt("DG differential ghost constant")(1, 0::0::Nil) &
        useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::0::0::Nil) &
        useAt(allDual_y, PosInExpr(0::Nil))(1, 0::Nil) &
        useAt("<> diamond", PosInExpr(0::Nil))(1, 0::0::Nil) &
        byUS(equivReflexiveAxiom)
    )

  @Axiom("DGCdc", "DGCdc")
  lazy val DGCddifferentialghostconstconv = derivedAxiom("DGd diamond differential ghost constant converse",
    Sequent(IndexedSeq(), IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\forall y_ <{y_'=b(|y_|),c{|y_|}&q(|y_|)}>p(|y_|)".asFormula)),
      useAt(proveBy("<{c,d&q(||)}>p(||) <-> <{d,c&q(||)}>p(||)".asFormula, useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
        useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
        useAt(proveBy("(!p() <-> !q()) <-> (p() <-> q())".asFormula, TactixLibrary.prop))(1) &
        byUS(", commute")))(1,PosInExpr(1::0::Nil)) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("DG differential ghost constant")(1, 0::0::Nil) &
      useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::0::0::Nil) &
      useAt(allDual_y, PosInExpr(0::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(0::Nil))(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  @Axiom("DGCde", "DGCde")
  lazy val DGCddifferentialghostconstexists =
    derivedAxiom("DGd diamond differential ghost constant exists",
      Sequent(IndexedSeq(), IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\exists y_ <{c{|y_|},y_'=b(|y_|)&q(|y_|)}>p(|y_|)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
        useAt("<> diamond", PosInExpr(1::Nil))(1, 1::0::Nil) &
        useAt("DG differential ghost constant all")(1, 0::0::Nil) &
        useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 1::Nil) &
        useAt(allDual_y, PosInExpr(0::Nil))(1, 1::0::Nil) &
        byUS(equivReflexiveAxiom)
    )

  /**
    * {{{Axiom "DWd diamond differential weakening".
    *    <{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)&p_(||))
    * End.
    * }}}
    */
  @Axiom("DWd", "DWd")
  lazy val DWddifferentialweakening = derivedAxiom("DWd diamond differential weakening",
    Sequent(IndexedSeq(), IndexedSeq("<{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)&p_(||))".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt(proveBy("!(p_() & q_()) <-> (p_() -> !q_())".asFormula, TactixLibrary.prop))(1, 1::0::1::Nil) &
      useAt(DWeakening, PosInExpr(1::Nil))(1, 1::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "DWd2 diamond differential weakening".
    *    <{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)->p_(||))
    * End.
    * }}}
    */
  @Axiom("DWd2", "DWd2")
  lazy val DWd2differentialweakening = derivedAxiom("DWd2 diamond differential weakening",
    Sequent(IndexedSeq(), IndexedSeq("<{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)->p_(||))".asFormula)),
      equivR(1) <(
        implyRi & CMon(PosInExpr(1::Nil)) & prop & done,
        cutAt("q_(||) & (q_(||)->p_(||))".asFormula)(1, 1::Nil) <(
          implyRi & useAt(Kd2Axiom, PosInExpr(1::Nil))(1) & byUS("DW base")
          ,
          cohideR(1) & CMon(PosInExpr(1::Nil)) & prop & done
          )
        )
  )

  /**
    * {{{Axiom "DCd diamond differential cut".
    *   (<{c&q(||)}>p(||) <-> <{c&(q(||)&r(||))}>p(||)) <- [{c&q(||)}]r(||)
    *   // (<x'=f(x)&q(x); >p(x) <-> <x'=f(x)&(q(x)&r(x));>p(x)) <- [x'=f(x)&q(x);]r(x) THEORY
    * End.
    * }}}
    */
  @Axiom("DCd", "DCd", key = 1::0::Nil, recursor = Nil::Nil)
  lazy val DCddifferentialcut = derivedAxiom("DCd diamond differential cut",
    Sequent(IndexedSeq(), IndexedSeq("(<{c&q(||)}>p(||) <-> <{c&(q(||)&r(||))}>p(||)) <- [{c&q(||)}]r(||)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::Nil) &
      useAt(proveBy("(!p() <-> !q()) <-> (p() <-> q())".asFormula, TactixLibrary.prop))(1, 1::Nil) &
      byUS(DiffCut)
  )

  /**
    * {{{Axiom "leave within closed <=".
    *    (<{c&q}>p<=0 <-> <{c&q&p>=0}>p=0) <- p>=0
    * End.
    * }}}
    */
  @Axiom("leaveWithinClosed", "leaveWithinClosed", key = 1::0::Nil, recursor = Nil::Nil)
  lazy val leaveWithinClosed =
    derivedAxiom("leave within closed <=",
      "==>(<{c_{|t_|}&q_(|t_|)}>p_(|t_|)<=0 <-> <{c_{|t_|}&q_(|t_|)&p_(|t_|)>=0}>p_(|t_|)=0)<-p_(|t_|)>=0".asSequent,
      prop & Idioms.<(
        cut("[{c_{|t_|}&q_(|t_|)}]p_(|t_|)>=0".asFormula) & Idioms.<(
          dC("p_(|t_|)>=0".asFormula)(-2)& Idioms.<(
            useAt(DWddifferentialweakening)(-2) & useAt("<> diamond", PosInExpr(1::Nil))(1) & useAt("<> diamond", PosInExpr(1::Nil))(-2) & notR(1) & notL(-2) &
              generalize("(!p_(|t_|)=0)".asFormula)(1) & Idioms.<(closeId, useAt(equalExpand)(-1, 0::Nil) & useAt(flipGreaterEqual)(1, 0::0::1::Nil) & prop & done),
            closeId
          ),
          useAt("<> diamond", PosInExpr(1::Nil))(1) & notR(1) &
            useAt("RI& closed real induction >=", PosInExpr(0::Nil))(1) & prop & HilbertCalculus.composeb(1) &
            dC("!p_(|t_|)=0".asFormula)(1) & Idioms.<(
            useAt(DWeakening)(1) &
              TactixLibrary.generalize("true".asFormula)(1) & Idioms.<(cohideR(1) & HilbertCalculus.boxTrue(1), nil) /* TODO: Goedel? */ &
              implyR(1) &
              TactixLibrary.generalize("t_=0".asFormula)(1)& Idioms.<(cohideR(1) & assignb(1) & byUS(equalReflex), nil) /* TODO: assignb? */ &
              implyR(1) &
              dR("p_(|t_|)>0".asFormula)(1) & Idioms.<(
              useAt("Cont continuous existence", PosInExpr(1::Nil))(1) &
                useAt(greaterEqual)(-1, 1::1::0::Nil) &
                prop &
                done,
              useAt(DWeakening)(1) &
                TactixLibrary.generalize("true".asFormula)(1) & Idioms.<(cohideR(1) & HilbertCalculus.boxTrue(1), nil) /* TODO: Goedel? */ &
                useAt(greaterEqual)(1, 1::Nil) &
                prop &
                done
            ),
            closeId)
        ),
        dR("q_(|t_|)".asFormula)(-2) & Idioms.<(
          useAt("<> diamond", PosInExpr(1::Nil))(1) & notR(1) &
            useAt("<> diamond", PosInExpr(1::Nil))(-2) & notL(-2) &
            TactixLibrary.generalize("!p_(|t_|)<=0".asFormula)(1) & Idioms.<(closeId, useAt(lessEqual)(-1,0::Nil) & prop & done),
          useAt(DWeakening)(1) &
            TactixLibrary.generalize("true".asFormula)(1) & Idioms.<(cohideR(1) & HilbertCalculus.boxTrue(1), prop & done) /* TODO: Goedel? */)
      )
    )

  /**
    * {{{Axiom "open invariant closure >".
    *    ([{c&q}]p>0 <-> [{c&q&p>=0}]p>0) <- p>=0
    * End.
    * }}}
    */
  @Axiom("openInvariantClosure", "openInvariantClosure", key = 1::0::Nil, recursor = Nil::Nil)
  lazy val openInvariantClosure =
    derivedAxiom("open invariant closure >",
      "==>([{c_{|t_|}&q_(|t_|)}]p_(|t_|)>0 <-> [{c_{|t_|}&q_(|t_|)&p_(|t_|)>=0}]p_(|t_|)>0) <- p_(|t_|)>=0".asSequent,
      implyR(1) &
        useAt(boxAxiom, PosInExpr(1::Nil))(1,0::Nil) &
        useAt(boxAxiom, PosInExpr(1::Nil))(1,1::Nil) &
        useAt(notGreater)(1,0::0::1::Nil) &
        prop & Idioms.<(
        useAt(leaveWithinClosed, PosInExpr(1::0::Nil))(1) & Idioms.<(
          useAt("<> diamond", PosInExpr(1::Nil))(1) & useAt("<> diamond", PosInExpr(1::Nil))(-2) & prop &
            DW(1) & generalize("!p_(|t_|)=0".asFormula)(1) & Idioms.<(closeId, useAt(greaterEqual)(1, 0::1::Nil) & prop & done),
          closeId),
        useAt(leaveWithinClosed, PosInExpr(1::0::Nil))(-2) & Idioms.<(
          useAt("<> diamond", PosInExpr(1::Nil))(1) & useAt("<> diamond", PosInExpr(1::Nil))(-2) & prop &
            generalize("!!p_(|t_|)>0".asFormula)(1) & Idioms.<(closeId, useAt(gtzImpNez)(-1,0::0::Nil) & useAt(notNotEqual)(-1,0::Nil) & closeId),
          closeId)
      )
    )

  /**
    * {{{Axiom "DCd diamond differential cut".
    *   (<{c&q(||)}>p(||) <-> <{c&(q(||)&r(||))}>p(||)) <- [{c&q(||)}]r(||)
    *   // (<x'=f(x)&q(x); >p(x) <-> <x'=f(x)&(q(x)&r(x));>p(x)) <- [x'=f(x)&q(x);]r(x) THEORY
    * End.
    * }}}
    */
  @Axiom("commaCommuted", "commaCommuted")
  lazy val commaCommuted = derivedAxiom(",d commute",
    Sequent(IndexedSeq(), IndexedSeq("<{c,d&q(||)}>p(||) <-> <{d,c&q(||)}>p(||)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt(proveBy("(!p() <-> !q()) <-> (p() <-> q())".asFormula, TactixLibrary.prop))(1) &
      byUS(", commute")
  )

  private val dbx_internal = Variable("y_", None, Real)
  /**
    * {{{Axiom "DBX>".
    *   (e>0 -> [c&q(||)]e>0) <- [c&q(||)](e)'>=g*e
    * End.
    * }}}
    * @note More precisely: this derivation assumes that y_ does not occur, hence the more fancy space dependents.
    * @see André Platzer and Yong Kiam Tan. Differential Equation Invariance Axiomatization. arXiv:1905.13429, May 2019.
    * @see [[darbouxOpenGt]]
    */
  @Axiom("DBX>", "DBXgt")
  lazy val darbouxGt =
    derivedAxiom("DBX>",
    Sequent(IndexedSeq(), IndexedSeq("(e(|y_|)>0 -> [{c{|y_|}&q(|y_|)}]e(|y_|)>0) <- [{c{|y_|}&q(|y_|)}](e(|y_|))'>=g(|y_|)*e(|y_|)".asFormula)),
    implyR(1) & implyR(1) &
      dG(AtomicODE(DifferentialSymbol(dbx_internal), Times(Neg(Divide("g(|y_|)".asTerm,Number(BigDecimal(2)))), dbx_internal)), None /*Some("e(|y_|)*y_^2>0".asFormula)*/)(1) &
      useAt(CoreAxiomInfo("DG inverse differential ghost"), (us:Option[Subst])=>us.getOrElse(throw new BelleUnsupportedFailure("DG expects substitution result from unification")) ++ RenUSubst(
        //(Variable("y_",None,Real), dbx_internal) ::
        (UnitFunctional("a", Except(Variable("y_", None, Real)::Nil), Real), Neg(Divide("g(|y_|)".asTerm,Number(BigDecimal(2))))) ::
          (UnitFunctional("b", Except(Variable("y_", None, Real)::Nil), Real), Number(BigDecimal(0))) :: Nil))(-1) &
      //The following replicates functionality of existsR(Number(1))(1)
      // 1) Stutter
      cutLR("\\exists y_ [y_:=y_;][{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e(|y_|)>0".asFormula)(1,0::Nil) <(
        cutLR("[y_:=1;][{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e(|y_|)>0".asFormula)(1) <(
          //2) assignb
          useAt(assignbEquality_y)(1) &
          ProofRuleTactics.skolemizeR(1) & implyR(1),
          //3) finish up
          cohide(1) & CMon(PosInExpr(Nil)) &
          byUS(existsGeneralizey,(us: Subst) => RenUSubst(("f()".asTerm, Number(1)) :: ("p_(.)".asFormula, Box(Assign("y_".asVariable, DotTerm()), "[{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e(|y_|)>0".asFormula)) :: Nil))
          )
          ,
          cohide(1) & equivifyR(1) & CE(PosInExpr(0::Nil)) & byUS(selfAssign_y) & done
        ) &
      useAt(allEliminate_y, PosInExpr(0::Nil))(-1) & //allL/*(dbx_internal)*/(-1) &
      useAt(", commute")(-1) & //@note since DG inverse differential ghost has flipped order
      cutR("[{c{|y_|},y_'=(-(g(|y_|)/2))*y_+0&q(|y_|)}]e(|y_|)*y_^2>0".asFormula)(1) <(
        useAt(DIinvariant)(1) & implyR(1) & andR(1) <(
          hideL(-4) & hideL(-1) &  byUS(TactixLibrary.proveBy(Sequent(IndexedSeq("e()>0".asFormula,"y()=1".asFormula), IndexedSeq("e()*y()^2>0".asFormula)), QE & done)),
          derive(1, PosInExpr(1::Nil)) &
          useAt(", commute")(1) & useAt(DEdifferentialEffectSystem_y)(1) &
          useAt(assignDAxiomby, PosInExpr(0::Nil))(1, PosInExpr(1::Nil)) &
          cohide2(-1,1) & monb &
          // DebuggingTactics.print("DI finished") &
          byUS(TactixLibrary.proveBy(Sequent(IndexedSeq("ep()>=g()*e()".asFormula), IndexedSeq("ep()*y()^2 + e()*(2*y()^(2-1)*((-g()/2)*y()+0))>=0".asFormula)), QE & done))
          ),
          implyR(1) &
            // DebuggingTactics.print("new post") &
            cohide2(-4, 1) & monb & byUS(TactixLibrary.proveBy(Sequent(IndexedSeq("e()*y()^2>0".asFormula), IndexedSeq("e()>0".asFormula)), QE & done))
        )
    )

  /**
    * {{{Axiom "DBX> open".
    *   (e>0 -> [c&q(||)]e>0) <- [c&q(||)](e>0 -> (e)'>=g*e)
    * End.
    * }}}
    * @note More precisely: this derivation assumes that y_ does not occur, hence the more fancy space dependents.
    * @see André Platzer and Yong Kiam Tan. Differential Equation Invariance Axiomatization. arXiv:1905.13429, May 2019.
    * @see [[darbouxGt]]
    */
  @Axiom("DBX> open", "DBXgtOpen")
  lazy val darbouxOpenGt =
    derivedAxiom("DBX> open",
      Sequent(IndexedSeq(), IndexedSeq("(e(|y_|)>0 -> [{c{|y_|}&q(|y_|)}]e(|y_|)>0) <- [{c{|y_|}&q(|y_|)}](e(|y_|) > 0 -> (e(|y_|)'>=g(|y_|)*e(|y_|)))".asFormula)),
      implyR(1) & implyR(1) &
        dG(AtomicODE(DifferentialSymbol(dbx_internal), Times(Neg(Divide("g(|y_|)".asTerm,Number(BigDecimal(2)))), dbx_internal)), None /*Some("e(|y_|)*y_^2>0".asFormula)*/)(1) &
        useAt(CoreAxiomInfo("DG inverse differential ghost"), (us:Option[Subst])=>us.getOrElse(throw new BelleUnsupportedFailure("DG expects substitution result from unification")) ++ RenUSubst(
          //(Variable("y_",None,Real), dbx_internal) ::
          (UnitFunctional("a", Except(Variable("y_", None, Real)::Nil), Real), Neg(Divide("g(|y_|)".asTerm,Number(BigDecimal(2))))) ::
            (UnitFunctional("b", Except(Variable("y_", None, Real)::Nil), Real), Number(BigDecimal(0))) :: Nil))(-1) &
        //The following replicates functionality of existsR(Number(1))(1)
        // 1) Stutter
        cutLR("\\exists y_ [y_:=y_;][{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e(|y_|)>0".asFormula)(1,0::Nil) <(
          cutLR("[y_:=1;][{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e(|y_|)>0".asFormula)(1) <(
            //2) assignb
            useAt(assignbEquality_y)(1) &
              ProofRuleTactics.skolemizeR(1) & implyR(1),
            //3) finish up
            cohide(1) & CMon(PosInExpr(Nil)) &
              byUS(existsGeneralizey,(us: Subst) => RenUSubst(("f()".asTerm, Number(1)) :: ("p_(.)".asFormula, Box(Assign("y_".asVariable, DotTerm()), "[{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e(|y_|)>0".asFormula)) :: Nil))
          )
          ,
          cohide(1) & equivifyR(1) & CE(PosInExpr(0::Nil)) & byUS(selfAssign_y) & done
        ) &
        useAt(allEliminate_y, PosInExpr(0::Nil))(-1) & //allL/*(dbx_internal)*/(-1) &
        useAt(", commute")(-1) & //@note since DG inverse differential ghost has flipped order
        cutR("[{c{|y_|},y_'=(-(g(|y_|)/2))*y_+0&q(|y_|)}]e(|y_|)*y_^2>0".asFormula)(1) <(
          useAt("DIo open differential invariance >")(1) <(
            HilbertCalculus.testb(1) & implyR(1) & hideL(-4) & hideL(-1) &  byUS(TactixLibrary.proveBy(Sequent(IndexedSeq("e()>0".asFormula,"y()=1".asFormula), IndexedSeq("e()*y()^2>0".asFormula)), QE & done)),
            implyR(1) & hideL(-4) &
              derive(1, PosInExpr(1::1::Nil)) &
              useAt(", commute")(1) & useAt(DEdifferentialEffectSystem_y)(1) &
              useAt(assignDAxiomby, PosInExpr(0::Nil))(1, PosInExpr(1::Nil)) &
              cohide2(-1,1) & monb &
              // DebuggingTactics.print("DI finished") &
              byUS(TactixLibrary.proveBy(Sequent(IndexedSeq("e() > 0 -> ep()>=g()*e()".asFormula), IndexedSeq("e()*y()^2 >0 -> ep()*y()^2 + e()*(2*y()^(2-1)*((-g()/2)*y()+0))>=0".asFormula)), QE & done))
          ),
          implyR(1) &
            // DebuggingTactics.print("new post") &
            cohide2(-4, 1) & monb & byUS(TactixLibrary.proveBy(Sequent(IndexedSeq("e()*y()^2>0".asFormula), IndexedSeq("e()>0".asFormula)), QE & done))
        )
    )

  /**
    * {{{
    *   Axiom "[d] dual".
    *    [{a;}^@]p(||) <-> ![a;]!p(||)
    *   End.
    * }}}
    * @derived
    */
  @Axiom(("[d]", "[d]"), codeName = "dualb", formula = "<span class=\"k4-axiom-key\">[a<sup>d</sup>]P</span>↔¬[a]¬P", unifier = "linear",
    key =  0::Nil, recursor = (0::Nil)::Nil)
  lazy val dualbAxiom =
    derivedAxiom("[d] dual",
      Sequent(IndexedSeq(), IndexedSeq("[{a;}^@]p(||) <-> ![a;]!p(||)".asFormula)),
      useAt(boxAxiom, AxiomIndex.axiomIndex("box []")._1.sibling)(1, 0::Nil) &
        useAt("<d> dual")(1, 0::0::Nil) &
        useAt(boxAxiom)(1, 0::0::Nil) &
        byUS(equivReflexiveAxiom)
    )
  /**
    * {{{
    *   Axiom "[d] dual direct".
    *    [{a;}^@]p(||) <-> <a;>p(||)
    *   End.
    * }}}
    * @derived
    */
  @Axiom(("[d]", "[d]"), "dualDirectb", formula = "<span class=\"k4-axiom-key\">[a<sup>d</sup>]P</span>↔&langle;a&rangle;P"
    , unifier = "linear", key = 0::Nil, recursor = (0::Nil)::Nil)
  lazy val dualbDirectAxiom = derivedAxiom("[d] dual direct",
    Sequent(IndexedSeq(), IndexedSeq("[{a;}^@]p(||) <-> <a;>p(||)".asFormula)),
    useExpansionAt("<> diamond")(1, 1::Nil) &
      byUS(dualbAxiom)
  )

  /**
    * {{{
    *   Axiom "<d> dual direct".
    *    <{a;}^@>p(||) <-> [a;]p(||)
    *   End.
    * }}}
    * @derived
    */
  @Axiom(("<d>", "<d>"), "dualDirectd", formula = "<span class=\"k4-axiom-key\">&langle;a<sup>d</sup>&rangle;P</span>↔[a]P"
    , unifier = "linear", key = 0::Nil, recursor = (0::Nil)::Nil)
  lazy val dualdDirectAxiom =
    derivedAxiom("<d> dual direct",
      Sequent(IndexedSeq(), IndexedSeq("<{a;}^@>p(||) <-> [a;]p(||)".asFormula)),
      useAt(boxAxiom, AxiomIndex.axiomIndex("box []")._1.sibling)(1, 1::Nil) &
        byUS("<d> dual")
    )

  // differentials

  /**
    * {{{Axiom "x' derive var commuted".
    *    (x_') = (x_)'
    * End.
    * }}}
    */
  @Axiom(("x',C","x',C"), "DvariableCommutedAxiom", formula = "x'=<span class=\"k4-axiom-key\">(x)'</span>"
    , unifier = "linear")
  lazy val DvariableCommuted = derivedAxiom("x' derive var commuted",
    Sequent(IndexedSeq(), IndexedSeq("(x_') = (x_)'".asFormula)),
    useAt(equalCommute)(1) &
      byUS("x' derive var")
  )

  /**
    * {{{Axiom "x' derive variable".
    *    \forall x_ ((x_)' = x_')
    * End.
    * }}}
    */
  @Axiom(("x'","x'"), "DvariableAxiom", formula = "<span class=\"k4-axiom-key\">(x)'</span>=x'")
  lazy val Dvariable = derivedFact("x' derive variable",
    DerivedAxiomProvableSig.startProof(Sequent(IndexedSeq(), IndexedSeq("\\forall x_ ((x_)' = x_')".asFormula)))
    (Skolemize(SuccPos(0)), 0)
    (DerivedAxiomProvableSig.axioms("x' derive var"), 0)
  )
  //  /**
  //   * {{{Axiom "x' derive var".
  //   *    (x_)' = x_'
  //   * End.
  //   * }}}
  //   * @todo derive
  //   */
  //  lazy val DvarF = "((x_)' = x_')".asFormula
  //  lazy val Dvar = derivedAxiom("'x derive var",
  //    Provable.startProof(Sequent(IndexedSeq(), IndexedSeq(DvarF)))
  //      (CutRight("\\forall x_ ((x_)' = x_')".asFormula, SuccPos(0)), 0)
  //      // right branch
  //      (UniformSubstitutionRule.UniformSubstitutionRuleForward(Axiom.axiom("all eliminate"),
  //        USubst(SubstitutionPair(PredOf(Function("p_",None,Real,Bool),Anything), DvarF)::Nil)), 0)
  //      // left branch
  //      (Axiom.axiom("x' derive variable"), 0)
  //    /*TacticLibrary.instantiateQuanT(Variable("x_",None,Real), Variable("x",None,Real))(1) &
  //      byUS("= reflexive")*/
  //  )
  //  lazy val DvarT = TactixLibrary.byUS(Dvar)
  /**
    * {{{Axiom "' linear".
    *    (c()*f(||))' = c()*(f(||))'
    * End.
    * }}}
    */
  @Axiom(("l'","l'"), "Dlinear", unifier = "linear", key = 0::Nil, recursor = (1::Nil)::Nil)
  lazy val Dlinear =
    derivedAxiom("' linear",
      Sequent(IndexedSeq(), IndexedSeq("(c_()*f_(||))' = c_()*(f_(||))'".asFormula)),
      useAt("*' derive product")(1, 0::Nil) &
        useAt("c()' derive constant fn")(1, 0::0::0::Nil) &
        useAt(zeroTimes)(1, 0::0::Nil) &
        useAt(zeroPlus)(1, 0::Nil) &
        byUS(equalReflex)
    )

  /**
    * {{{Axiom "' linear right".
    *    (f(||)*c())' = f(||)'*c()
    * End.
    * }}}
    */
  @Axiom(("l'","l'"), "DlinearRight", unifier = "linear", key = 0::Nil, recursor = (0::Nil)::Nil)
  lazy val DlinearRight = derivedAxiom("' linear right",
    Sequent(IndexedSeq(), IndexedSeq("(f(||)*c())' = (f(||))'*c()".asFormula)),
    useAt("*' derive product")(1, 0:: Nil) &
      useAt("c()' derive constant fn")(1, 0:: 1::1::Nil) &
      useAt(timesZero)(1, 0:: 1::Nil) &
      useAt(plusZero)(1, 0:: Nil) &
      byUS(equalReflex)
  )
  //@note elegant proof that clashes for some reason
  //  derivedAxiom("' linear right",
  //  Sequent(IndexedSeq(), IndexedSeq(DlinearRightF)),
  //  useAt("* commute")(1, 0::0::Nil) &
  //    useAt("* commute")(1, 1::Nil) &
  //    by(Dlinear)
  //)

  /**
    * {{{Axiom "Uniq uniqueness iff"
    *    <{c&q(||)}>p(||) & <{c&r(||)}>p(||) <-> <{c & q(||)&q(||)}>(p(||))
    * End.
    * }}}
    */
  @Axiom("Uniq", "UniqIff")
  lazy val uniquenessIff = derivedFormula("Uniq uniqueness iff",
    "<{c&q(||)}>p(||) & <{c&r(||)}>p(||) <-> <{c&q(||) & r(||)}>p(||)".asFormula,
    equivR(1) <(
      implyRi & byUS("Uniq uniqueness"),
      andR(1) <(
        dR("q(||)&r(||)".asFormula)(1)<( closeId, DW(1) & G(1) & prop),
        dR("q(||)&r(||)".asFormula)(1)<( closeId, DW(1) & G(1) & prop)
        )
    )
  )

  // real arithmetic

  /**
   * {{{Axiom "= reflexive".
   *    s() = s()
   * End.
   * }}}
    * @see [[equivReflexiveAxiom]]
   */
  @Axiom("=R", "equalReflexive", unifier = "full")
  lazy val equalReflex =
    derivedAxiom("= reflexive", Sequent(IndexedSeq(), IndexedSeq("s_() = s_()".asFormula)),
      allInstantiateInverse(("s_()".asTerm, "x".asVariable))(1) &
        byUS(proveBy("\\forall x x=x".asFormula, TactixLibrary.RCF))
    )

  /**
    * {{{Axiom "= commute".
    *   (f()=g()) <-> (g()=f())
    * End.
    * }}}
    */
  @Axiom("=C", "equalCommute", unifier = "linear")
  lazy val equalCommute = derivedAxiom("= commute", Sequent(IndexedSeq(), IndexedSeq("(f_()=g_()) <-> (g_()=f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x=y <-> y=x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom ">= reflexive".
    *    s() >= s()
    * End.
    * }}}
    */
  @Axiom(">=R", "greaterEqualReflexive", unifier = "full")
  lazy val greaterEqualReflex = derivedAxiom(">= reflexive", Sequent(IndexedSeq(), IndexedSeq("s_() >= s_()".asFormula)), QE & done)

  /**
    * {{{Axiom "* commute".
    *   (f()*g()) = (g()*f())
    * End.
    * }}}
    */
  lazy val timesCommute = timesCommutative

  /**
    * {{{Axiom "<=".
    *   (f()<=g()) <-> ((f()<g()) | (f()=g()))
    * End.
    * }}}
    */
  @Axiom("<=", "lessEqual", unifier = "linear")
  lazy val lessEqual = derivedAxiom("<=", Sequent(IndexedSeq(), IndexedSeq("(f_()<=g_()) <-> ((f_()<g_()) | (f_()=g_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x<=y <-> (x<y | x=y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom ">=".
    *   (f()>=g()) <-> ((f()>g()) | (f()=g()))
    * End.
    * }}}
    */
  @Axiom(">=", "greaterEqual", unifier = "linear")
  lazy val greaterEqual = derivedAxiom(">=", Sequent(IndexedSeq(), IndexedSeq("(f_()>=g_()) <-> ((f_()>g_()) | (f_()=g_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (x>=y <-> (x>y | x=y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "! !=".
    *   (!(f() != g())) <-> (f() = g())
    * End.
    * }}}
    */
  @Axiom(("¬≠","!!="), "notNotEqual", formula = "<span class=\"k4-axiom-key\">(¬(f≠g)</span>↔(f=g))"
    , unifier ="linear")
  lazy val notNotEqual = derivedAxiom("! !=", Sequent(IndexedSeq(), IndexedSeq("(!(f_() != g_())) <-> (f_() = g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((!(x != y)) <-> (x = y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "! =".
    *   !(f() = g()) <-> f() != g()
    * End.
    * }}}
    */
  @Axiom(("¬ =","! ="), "notEqual", formula = "<span class=\"k4-axiom-key\">(¬(f=g))</span>↔(f≠g)"
  , unifier = "linear")
  lazy val notEqual = derivedAxiom("! =", Sequent(IndexedSeq(), IndexedSeq("(!(f_() = g_())) <-> (f_() != g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((!(x = y)) <-> (x != y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "! >".
    *   (!(f() > g())) <-> (f() <= g())
    * End.
    * }}}
    */
  @Axiom(("¬>","!>"), "notGreater", formula = "<span class=\"k4-axiom-key\">¬(f>g)</span>↔(f≤g)"
    , unifier ="linear")
  lazy val notGreater = derivedAxiom("! >", Sequent(IndexedSeq(), IndexedSeq("(!(f_() > g_())) <-> (f_() <= g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((!(x > y)) <-> (x <= y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "> flip".
    *   (f() > g()) <-> (g() < f())
    * End.
    * */
  @Axiom(">F", "flipGreater", unifier = "linear", key = 0::Nil, recursor = Nil::Nil)
  lazy val flipGreater = derivedAxiom("> flip", Sequent(IndexedSeq(), IndexedSeq("(f_() > g_()) <-> (g_() < f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((x > y) <-> (y < x))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom ">= flip".
    *   (f() >= g()) <-> (g() <= f())
    * End.
    * }}}
    */
  @Axiom(">=F", "flipGreaterEqual", unifier = "linear", key = 0::Nil, recursor = Nil::Nil)
  lazy val flipGreaterEqual = derivedAxiom(">= flip", Sequent(IndexedSeq(), IndexedSeq("(f_() >= g_()) <-> (g_() <= f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((x >= y) <-> (y <= x))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "< flip".
    *   (f() < g()) <-> (g() > f())
    * End.
    * */
  @Axiom("<F", "flipLess", unifier = "linear")
  lazy val flipLess = derivedAxiom("< flip", Sequent(IndexedSeq(), IndexedSeq("(f_() < g_()) <-> (g_() > f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((x < y) <-> (y > x))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<= flip".
    *   (f() <= g()) <-> (g() >= f())
    * End.
    * }}}
    */
  @Axiom("<=F", "flipLessEqual", unifier = "linear")
  lazy val flipLessEqual = derivedAxiom("<= flip", Sequent(IndexedSeq(), IndexedSeq("(f_() <= g_()) <-> (g_() >= f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((x <= y) <-> (y >= x))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "! <".
    *   (!(f() < g())) <-> (f() >= g())
    * End.
    * }}}
    */
  @Axiom(("¬<","!<"), "notLess", formula = "<span class=\"k4-axiom-key\">¬(f<g)</span>↔(f≥g)", unifier ="linear")
  lazy val notLess = derivedAxiom("! <", Sequent(IndexedSeq(), IndexedSeq("(!(f_() < g_())) <-> (f_() >= g_())".asFormula)),
    useAt(flipGreater, PosInExpr(1::Nil))(1, 0::0::Nil) & useAt(notGreater)(1, 0::Nil) & useAt(flipGreaterEqual)(1, 1::Nil) & byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "! <=".
    *   (!(f() <= g())) <-> (f() > g())
    * End.
    * }}}
    */
  @Axiom(("¬≤","!<="), "notLessEqual", formula = "<span class=\"k4-axiom-key\">(¬(f≤g)</span>↔(f>g)", unifier = "linear")
  lazy val notLessEqual = derivedAxiom("! <=", Sequent(IndexedSeq(), IndexedSeq("(!(f_() <= g_())) <-> (f_() > g_())".asFormula)),
    useAt(flipGreaterEqual, PosInExpr(1::Nil))(1, 0::0::Nil) & useAt(notGreaterEqual)(1, 0::Nil) & useAt(flipGreater)(1, 1::Nil) & byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "! >=".
    *   (!(f() >= g())) <-> (f() < g())
    * End.
    * }}}
    */
  @Axiom(("¬≥","!>="), "notGreaterEqual", unifier = "linear")
  lazy val notGreaterEqual = derivedAxiom("! >=", Sequent(IndexedSeq(), IndexedSeq("(!(f_() >= g_())) <-> (f_() < g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((!(x >= y)) <-> (x < y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+ associative".
    *    (f()+g()) + h() = f() + (g()+h())
    * End.
    * }}}
    */
  @Axiom("+A", "plusAssociative", unifier = "linear")
  lazy val plusAssociative = derivedAxiom("+ associative", Sequent(IndexedSeq(), IndexedSeq("(f_() + g_()) + h_() = f_() + (g_() + h_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x ((x + y) + z = x + (y + z))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "* associative".
    *    (f()*g()) * h() = f() * (g()*h())
    * End.
    * }}}
    */
  @Axiom("*A", "timesAssociative", unifier = "linear")
  lazy val timesAssociative = derivedAxiom("* associative", Sequent(IndexedSeq(), IndexedSeq("(f_() * g_()) * h_() = f_() * (g_() * h_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x ((x * y) * z = x * (y * z))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+ commute".
    *    f()+g() = g()+f()
    * End.
    * }}}
    */
  @Axiom("+C", "plusCommute", unifier = "linear")
  lazy val plusCommutative = derivedAxiom("+ commute", Sequent(IndexedSeq(), IndexedSeq("f_()+g_() = g_()+f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x+y = y+x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "* commute".
    *    f()*g() = g()*f()
    * End.
    * }}}
    */
  @Axiom("*C", "timesCommute", unifier = "linear")
  lazy val timesCommutative = derivedAxiom("* commute", Sequent(IndexedSeq(), IndexedSeq("f_()*g_() = g_()*f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x*y = y*x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "distributive".
    *    f()*(g()+h()) = f()*g() + f()*h()
    * End.
    * }}}
    */
  @Axiom("*+", "distributive")
  lazy val distributive = derivedAxiom("distributive", Sequent(IndexedSeq(), IndexedSeq("f_()*(g_()+h_()) = f_()*g_() + f_()*h_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x (x*(y+z) = x*y + x*z)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+ identity".
    *    f()+0 = f()
    * End.
    * }}}
    */
  lazy val plusIdentity = zeroPlus

  /**
    * {{{Axiom "* identity".
    *    f()*1 = f()
    * End.
    * }}}
    */
  @Axiom("*I", "timesIdentity")
  lazy val timesIdentity = derivedAxiom("* identity", Sequent(IndexedSeq(), IndexedSeq("f_()*1 = f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
    byUS(proveBy("\\forall x (x*1 = x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+ inverse".
    *    f() + (-f()) = 0
    * End.
    * }}}
    */
  @Axiom("+i", "plusInverse", unifier = "full")
  lazy val plusInverse = derivedAxiom("+ inverse", Sequent(IndexedSeq(), IndexedSeq("f_() + (-f_()) = 0".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
    byUS(proveBy("\\forall x (x + (-x) = 0)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "* inverse".
    *    f() != 0 -> f()*(f()^-1) = 1
    * End.
    * }}}
    */
  @Axiom("*i", "timesInverse", unifier = "full")
  lazy val timesInverse = derivedAxiom("* inverse", Sequent(IndexedSeq(), IndexedSeq("f_() != 0 -> f_()*(f_()^-1) = 1".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
    byUS(proveBy("\\forall x (x != 0 -> x*(x^-1) = 1)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "positivity".
    *    f() < 0 | f() = 0 | 0 < f()
    * End.
    * }}}
    */
  @Axiom("Pos", "positivity")
  lazy val positivity = derivedAxiom("positivity", Sequent(IndexedSeq(), IndexedSeq("f_() < 0 | f_() = 0 | 0 < f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
    byUS(proveBy("\\forall x (x < 0 | x = 0 | 0 < x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+ closed".
    *    0 < f() & 0 < g() -> 0 < f()+g()
    * End.
    * }}}
    */
  @Axiom("+c", "plusClosed")
  lazy val plusClosed = derivedAxiom("+ closed", Sequent(IndexedSeq(), IndexedSeq("0 < f_() & 0 < g_() -> 0 < f_()+g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (0 < x & 0 < y -> 0 < x+y)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "* closed".
    *    0 < f() & 0 < g() -> 0 < f()*g()
    * End.
    * }}}
    */
  @Axiom("*c", "timesClosed")
  lazy val timesClosed = derivedAxiom("* closed", Sequent(IndexedSeq(), IndexedSeq("0 < f_() & 0 < g_() -> 0 < f_()*g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (0 < x & 0 < y -> 0 < x*y)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<".
    *    f() < g() <-> 0 < g()-f()
    * End.
    * }}}
    */
  @Axiom("<", "less", unifier = "linear")
  lazy val less = derivedAxiom("<", Sequent(IndexedSeq(), IndexedSeq("f_() < g_() <-> 0 < g_()-f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x < y <-> 0 < y-x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom ">".
    *    f() > g() <-> g() < f()
    * End.
    * }}}
    */
  @Axiom(">", "greater", unifier = "linear")
  lazy val greater = derivedAxiom(">", Sequent(IndexedSeq(), IndexedSeq("f_() > g_() <-> g_() < f_()".asFormula)), byUS(flipGreater))

  // built-in arithmetic

  /**
    * {{{Axiom "!= elimination".
    *   f()!=g() <-> \exists z (f()-g())*z=1
    * End.
    * }}}
    * @see André Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. CADE 2009.
    */
  //@note disabled since not provable with Z3; intended to replace QE with core implementation
//  lazy val notEqualElim = derivedAxiom("!= elimination", Sequent(IndexedSeq(), IndexedSeq("(f_()!=g_()) <-> \\exists z_ ((f_()-g_())*z_=1)".asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
//    byUS(proveBy("\\forall y \\forall x ((x!=y) <-> \\exists z_ ((x-y)*z_=1))".asFormula, TactixLibrary.RCF))
//  )

  /**
    * {{{Axiom ">= elimination".
    *   f()>=g() <-> \exists z f()-g()=z^2
    * End.
    * }}}
    * @see André Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. CADE 2009.
    */
  //@note disabled since not provable with Z3; intended to replace QE with core implementation
//  lazy val greaterEqualElim = derivedAxiom(">= elimination", Sequent(IndexedSeq(), IndexedSeq("(f_()>=g_()) <-> \\exists z_ (f_()-g_()=z_^2)".asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
//    byUS(proveBy("\\forall y \\forall x ((x>=y) <-> \\exists z_ (x-y=z_^2))".asFormula, TactixLibrary.RCF))
//  )

  /**
    * {{{Axiom "> elimination".
    *   f()>g() <-> \exists z (f()-g())*z^2=1
    * End.
    * }}}
    * @see André Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. CADE 2009.
    */
  //@note disabled since not provable with Z3; intended to replace QE with core implementation
//  lazy val greaterElim = derivedAxiom("> elimination", Sequent(IndexedSeq(), IndexedSeq("(f_()>g_()) <-> \\exists z_ ((f_()-g_())*z_^2=1)".asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
//    byUS(proveBy("\\forall y \\forall x ((x>y) <-> \\exists z_ ((x-y)*z_^2=1))".asFormula, TactixLibrary.RCF))
//  )

  /**
    * {{{Axiom "1>0".
    *   1>0
    * End.
    * }}}
    */
  @Axiom("1>0", "oneGreaterZero", unifier = "linear")
  lazy val oneGreaterZero = derivedAxiom("1>0", Sequent(IndexedSeq(), IndexedSeq("1>0".asFormula)), TactixLibrary.RCF)

  /**
    * {{{Axiom "nonnegative squares".
    *   f()^2>=0
    * End.
    * }}}
    */
  @Axiom("^2>=0", "nonnegativeSquares", unifier = "linear")
  lazy val nonnegativeSquares = derivedAxiom("nonnegative squares", Sequent(IndexedSeq(), IndexedSeq("f_()^2>=0".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
    byUS(proveBy("\\forall x (x^2>=0)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom ">2!=".
    *   f()>g() -> f()!=g()
    * End.
    * }}}
    */
  @Axiom(">2!=", "greaterImpliesNotEqual")
  lazy val greaterImpliesNotEqual = derivedAxiom(">2!=", Sequent(IndexedSeq(), IndexedSeq("f_()>g_() -> f_()!=g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x>y -> x!=y)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "> monotone".
    *   f()+h()>g() <- f()>g() & h()>=0
    * End.
    * }}}
    */
  @Axiom(">mon", "greaterMonotone")
  lazy val greaterMonotone = derivedAxiom("> monotone", Sequent(IndexedSeq(), IndexedSeq("f_()+h_()>g_() <- f_()>g_() & h_()>=0".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x (x+z>y <- x>y & z>=0)".asFormula, TactixLibrary.RCF))
  )

  // stuff

  /**
    * {{{Axiom "abs".
    *   (abs(s()) = t()) <->  ((s()>=0 & t()=s()) | (s()<0 & t()=-s()))
    * End.
    * }}}
    *
    * @Derived from built-in arithmetic abs in [[edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaQETool]]
    */
  @Axiom("abs", "abs")
  lazy val absDef = derivedAxiom("abs", Sequent(IndexedSeq(), IndexedSeq("(abs(s_()) = t_()) <->  ((s_()>=0 & t_()=s_()) | (s_()<0 & t_()=-s_()))".asFormula)),
    allInstantiateInverse(("s_()".asTerm, "x".asVariable), ("t_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((abs(x) = y) <->  ((x>=0 & y=x) | (x<0 & y=-x)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "min".
    *    (min(f(), g()) = h()) <-> ((f()<=g() & h()=f()) | (f()>g() & h()=g()))
    * End.
    * }}}
    *
    * @Derived from built-in arithmetic abs in [[edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaQETool]]
    */
  @Axiom("min", "min")
  lazy val minDef = derivedAxiom("min", Sequent(IndexedSeq(), IndexedSeq("(min(f_(), g_()) = h_()) <-> ((f_()<=g_() & h_()=f_()) | (f_()>g_() & h_()=g_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x ((min(x, y) = z) <-> ((x<=y & z=x) | (x>y & z=y)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "max".
    *    (max(f(), g()) = h()) <-> ((f()>=g() & h()=f()) | (f()<g() & h()=g()))
    * End.
    * }}}
    *
    * @Derived from built-in arithmetic abs in [[edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaQETool]]
    */
  @Axiom("max", "max")
  lazy val maxDef = derivedAxiom("max", Sequent(IndexedSeq(), IndexedSeq("(max(f_(), g_()) = h_()) <-> ((f_()>=g_() & h_()=f_()) | (f_()<g_() & h_()=g_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x ((max(x, y) = z) <-> ((x>=y & z=x) | (x<y & z=y)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<*> stuck".
    *    <{a;}*>p(||) <-> <{a;}*>p(||)
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */
  @Axiom("<*> stuck", "loopStuck", key =  0::Nil, recursor = Nil)
  lazy val loopStuck = derivedAxiom("<*> stuck",
    Sequent(IndexedSeq(), IndexedSeq("<{a_;}*>p_(||) <-> <{a_;}*>p_(||)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  @Axiom("<a> stuck", "programStuck", key = 0::Nil, recursor = (1::Nil)::Nil)
  lazy val programStuck = derivedAxiom("<a> stuck",
    Sequent(IndexedSeq(), IndexedSeq("<a_;>p_(||) <-> <a_;>p_(||)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<'> stuck".
    *    <{c&q(||)}>p(||) <-> <{c&q(||)}>p(||)
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */
  @Axiom(("<'> stuck","<'> stuck"), "odeStuck", key = 0::Nil, recursor = Nil)
  lazy val odeStuck = derivedAxiom("<'> stuck",
    Sequent(IndexedSeq(), IndexedSeq("<{c_&q_(||)}>p_(||) <-> <{c_&q_(||)}>p_(||)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "& recursor".
    *    p() & q() <-> p() & q()
    * End.
    * }}}
    *
    */
  @Axiom("& recursor", "andRecursor", unifier = "linear", key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  lazy val andRecursor = derivedAxiom("& recursor", Sequent(IndexedSeq(), IndexedSeq("(p_() & q_()) <-> (p_() & q_())".asFormula)), prop)

  /**
    * {{{Axiom "| recursor".
    *    p() | q() <-> p() | q()
    * End.
    * }}}
    *
    */
  @Axiom("| recursor", "orRecursor", unifier = "linear", key = 0::Nil, recursor = (0::Nil)::(1::Nil)::Nil)
  lazy val orRecursor = derivedAxiom("| recursor", Sequent(IndexedSeq(), IndexedSeq("(p_() | q_()) <-> (p_() | q_())".asFormula)), prop)

  /**
    * {{{Axiom "<= both".
    *    f()<=g() <- ((f() <= F() & gg() <= g()) & F() <= gg())
    * End.
    * }}}
    */
  @Axiom("<= both", "intervalLEBoth", key = 1::Nil, recursor = Nil)
  lazy val intervalLEBoth =
    derivedAxiom("<= both", Sequent(IndexedSeq(), IndexedSeq("f_()<=g_() <- ((f_()<=F_() & gg_()<=g_()) & F_() <= gg_())".asFormula)),
      allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("F_()".asTerm, "X".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
        byUS(proveBy("\\forall yy \\forall X \\forall y \\forall x (x<=y <- ((x<=X & yy<=y) & X<=yy))".asFormula, TactixLibrary.RCF))
    )

  /**
    * {{{Axiom "< both".
    *    f()<g() <- ((f() <= F() & gg() <= g()) & F() < gg())
    * End.
    * }}}
    */

  @Axiom("< both", "intervalLBoth", key = 1::Nil, recursor = Nil)
  lazy val intervalLBoth =
    derivedAxiom("< both", Sequent(IndexedSeq(), IndexedSeq("f_()<g_() <- ((f_()<=F_() & gg_()<=g_()) & F_() < gg_())".asFormula)),
      allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("F_()".asTerm, "X".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
        byUS(proveBy("\\forall yy \\forall X \\forall y \\forall x (x<y <- ((x<=X & yy<=y) & X<yy))".asFormula, TactixLibrary.RCF))
    )

  /**
    * {{{Axiom "neg<= up".
    *    -f()<=h() <- (ff()<=f() & -ff() <= h())
    * End.
    * }}}
    */
  @Axiom("neg<=", "intervalUpNeg", key = 1::Nil, recursor = (0::Nil)::Nil)
  lazy val intervalUpNeg = derivedAxiom("neg<= up", Sequent(IndexedSeq(), IndexedSeq("-f_()<=h_() <- (ff_() <= f_() & -ff_() <= h_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable))(1) &
      byUS(proveBy("\\forall xx \\forall z \\forall x (-x<=z <- (xx<=x & -xx <=z))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "abs<= up".
    *    abs(f())<=h() <- ((ff()<=f() & f() <= F()) & (-ff()<=h() & F()<=h()))
    * End.
    * }}}
    */

  @Axiom("abs<=", "intervalUpAbs", key = 1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalUpAbs = derivedAxiom("abs<= up", Sequent(IndexedSeq(), IndexedSeq("abs(f_())<=h_() <- ((ff_() <= f_() & f_() <= F_()) & (-ff_() <= h_() & F_()<= h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable),("F_()".asTerm,"X".asVariable))(1) &
      byUS(proveBy("\\forall X \\forall xx \\forall z \\forall x (abs(x)<=z <- ((xx<=x & x <=X) & (-xx <= z & X <= z)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "max<= up".
    *    max(f(),g())<=h() <- ((f()<=F() & g()<=G()) & (F() <= h() & G()<=h()))
    * End.
    * }}}
    */
  @Axiom("max<=", "intervalUpMax", key = 1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalUpMax = derivedAxiom("max<= up", Sequent(IndexedSeq(), IndexedSeq("max(f_(),g_())<=h_() <- ((f_()<=F_() & g_()<=G_()) & (F_() <= h_() & G_()<=h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable))(1) &
      byUS(proveBy("\\forall Y \\forall X \\forall z \\forall y \\forall x (max(x,y)<=z <- ((x<=X & y<=Y) & (X<=z & Y<=z)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "min<= up".
    *    min(f(),g())<=h() <- ((f()<=F() & g()<=G()) & (F()<=h() | G()<=h()))
    * End.
    * }}}
    */
  @Axiom("min<=", "intervalUpMin", key = 1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalUpMin = derivedAxiom("min<= up", Sequent(IndexedSeq(), IndexedSeq("min(f_(),g_())<=h_() <- ((f_()<=F_() & g_()<=G_()) & (F_() <= h_() | G_()<=h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable))(1) &
      byUS(proveBy("\\forall Y \\forall X \\forall z \\forall y \\forall x (min(x,y)<=z <- ((x<=X & y<=Y) & (X<=z | Y<=z)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+<= up".
    *    f()+g()<=h() <- ((f()<=F() & g()<=G()) & F()+G()<=h())
    * End.
    * }}}
    */
  @Axiom("+<=", "intervalUpPlus", key = 1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalUpPlus = derivedAxiom("+<= up", Sequent(IndexedSeq(), IndexedSeq("f_()+g_()<=h_() <- ((f_()<=F_() & g_()<=G_()) & F_()+G_()<=h_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable))(1) &
      byUS(proveBy("\\forall Y \\forall X \\forall z \\forall y \\forall x (x+y<=z <- ((x<=X & y<=Y) & X+Y<=z))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "-<= up".
    *    f()-g()<=h() <- ((f()<=F() & gg()<=g()) & F()-gg()<=h())
    * End.
    * }}}
    */
  @Axiom("-<=", "intervalUpMinus", key =  1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalUpMinus = derivedAxiom("-<= up", Sequent(IndexedSeq(), IndexedSeq("f_()-g_()<=h_() <- ((f_()<=F_() & gg_()<=g_()) & F_()-gg_()<=h_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall X \\forall z \\forall y \\forall x (x-y<=z <- ((x<=X & yy<=y) & X-yy<=z))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "*<= up".
    *    f()*g()<=h() <- ((ff()<=f() & f()<=F() & gg()<=g() & g()<=G()) & (ff()*gg()<=h() & ff()*G()<=h() & F()*gg()<=h() & F()*G()<=h()))
    * End.
    * }}}
    */
  // A more efficient check is available if we know that f_() or g_() is strictly positive
  // For example, if 0<= ff_(), then we only need ff_() * G_() <= h_() & F_() * G() <= h_()

  @Axiom("*<=", "intervalUpTimes", key = 1::Nil, recursor = (0::0::0::Nil)::(0::0::1::Nil)::(0::1::0::Nil)::(0::1::1::Nil)::Nil)
  lazy val intervalUpTimes = derivedAxiom("*<= up", Sequent(IndexedSeq(), IndexedSeq("f_()*g_()<=h_() <- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & (ff_()*gg_()<=h_() & ff_()*G_()<=h_() & F_()*gg_()<=h_() & F_()*G_()<=h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (x*y<=z <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & (xx*yy<=z & xx*Y<=z & X*yy<=z & X*Y<=z)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "1Div<= up".
    *    1/f()<=h() <- ((ff()<=f() & ff()*f()>0) & (1/ff()<=h()))
    * End.
    * }}}
    */
  @Axiom("1/<=", "intervalUp1Divide")
  lazy val intervalUp1Divide = derivedAxiom("1Div<= up", Sequent(IndexedSeq(), IndexedSeq("1/f_()<=h_() <- ((F_()<=f_() & F_()*f_()>0) & (1/F_()<=h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "y".asVariable), ("F_()".asTerm, "X".asVariable))(1) &
      byUS(proveBy("\\forall X \\forall y \\forall x (1/x<=y <- ((X<=x & X*x>0) & (1/X<=y)))".asFormula, TactixLibrary.RCF))
  )
  /**
    * {{{Axiom "Div<= up".
    *    f()/g()<=h() <- ((ff()<=f() & f()<=F() & gg()<=g() & g()<=G()) & ((G()<0 | 0<gg()) & (ff()/gg()<=h() & ff()/G()<=h() & F()/gg()<=h() & F()/G()<=h())))
    * End.
    * }}}
    */
  // A more efficient check is available

//  lazy val intervalUpDivide = derivedAxiom("Div<= up", Sequent(IndexedSeq(), IndexedSeq(("f_()/g_()<=h_() <- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & ((G_()<0 | 0<gg_()) & (ff_()/gg_()<=h_() & ff_()/G_()<=h_() & F_()/gg_()<=h_() & F_()/G_()<=h_())))").asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
//      byUS(proveBy("\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (x/y<=z <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & ((Y<0|0<yy) &(xx/yy<=z & xx/Y<=z & X/yy<=z & X/Y<=z))))".asFormula, TactixLibrary.RCF))
//  )

  /**
    * {{{Axiom "pow<= up".
    *    f()^2<=h() <- ((ff()<=f() & f()<=F()) & (ff()^2<=h() & F()^2<=h()))
    * End.
    * }}}
    */

  @Axiom("pow<=", "intervalUpPower", key = 1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalUpPower = derivedAxiom("pow<= up", Sequent(IndexedSeq(), IndexedSeq("f_()^2 <=h_() <- ((ff_()<=f_() & f_()<=F_()) & (ff_()^2 <= h_() & F_()^2 <=h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("ff_()".asTerm, "xx".asVariable))(1) &
      byUS(proveBy("\\forall xx \\forall X \\forall z \\forall x (x^2<=z <- ((xx<=x & x<=X) & (xx^2<=z & X^2<=z)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=neg down".
    *    h<=-f() <- (f()<=F() & h() <= -F())
    * End.
    * }}}
    */

  @Axiom("<=neg", "intervalDownNeg", key =  1::Nil, recursor = (0::Nil)::Nil)
  lazy val intervalDownNeg = derivedAxiom("<=neg down", Sequent(IndexedSeq(), IndexedSeq("h_()<=-f_() <- (f_() <= F_() & h_() <= -F_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable))(1) &
      byUS(proveBy("\\forall X \\forall z \\forall x (z<=-x <- (x<=X & z<=-X))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=abs down".
    *    h()<=abs(f()) <- ((ff()<=f() & f() <= F()) & (h()<=ff() | h()<=-F()))
    * End.
    * }}}
    */

  @Axiom("<=abs", "intervalDownAbs", key = 1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalDownAbs = derivedAxiom("<=abs down", Sequent(IndexedSeq(), IndexedSeq("h_()<=abs(f_()) <- ((ff_() <= f_() & f_() <= F_()) & (h_() <= ff_() | h_() <= -F_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable),("F_()".asTerm,"X".asVariable))(1) &
      byUS(proveBy("\\forall X \\forall xx \\forall z \\forall x (z<=abs(x) <- ((xx<=x & x <=X) & (z <= xx | z <= -X)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=max down".
    *    h()<=max(f(),g()) <- ((ff()<=f() & gg()<=g()) & (ff()<=h() | gg()<=h()))
    * End.
    * }}}
    */
  @Axiom("<=max", "intervalDownMax", key = 1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalDownMax = derivedAxiom("<=max down", Sequent(IndexedSeq(), IndexedSeq("h_() <= max(f_(),g_()) <- ((ff_()<=f_() & gg_()<=g_()) & (h_() <= ff_() | h_() <= gg_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall xx \\forall z \\forall y \\forall x (z <= max(x,y) <- ((xx<=x & yy<=y) & (z<=xx | z<=yy)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=min down".
    *    h()<=min(f(),g()) <- ((ff()<=f() & gg()<=g()) & (h()<=ff() & h()<=gg()))
    * End.
    * }}}
    */
  @Axiom("<=min", "intervalDownMin", key = 1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalDownMin = derivedAxiom("<=min down", Sequent(IndexedSeq(), IndexedSeq("h_()<=min(f_(),g_()) <- ((ff_()<=f_() & gg_()<=g_()) & (h_() <= ff_() & h_()<=gg_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall xx \\forall z \\forall y \\forall x (z<=min(x,y) <- ((xx<=x & yy<=y) & (z<=xx & z<=yy)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=+ down".
    *    h()<=f()+g() <- ((ff()<=f() & gg()<=g()) & h()<=ff()+gg())
    * End.
    * }}}
    */
  @Axiom("<=+", "intervalDownPlus", key = 1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalDownPlus = derivedAxiom("<=+ down", Sequent(IndexedSeq(), IndexedSeq("h_()<=f_()+g_() <- ((ff_()<=f_() & gg_()<=g_()) & h_()<=ff_()+gg_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall xx \\forall z \\forall y \\forall x (z<=x+y <- ((xx<=x & yy<=y) & z<=xx+yy))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=- down".
    *    h()<=f()-g() <- ((ff()<=f() & g()<=G()) & h()<=ff()-G())
    * End.
    * }}}
    */
  @Axiom("<=-", "intervalDownMinus", key = 1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalDownMinus = derivedAxiom("<=- down", Sequent(IndexedSeq(), IndexedSeq("h_()<=f_()-g_() <- ((ff_()<=f_() & g_()<=G_()) & h_()<=ff_()-G_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable), ("G_()".asTerm, "Y".asVariable))(1) &
      byUS(proveBy("\\forall Y \\forall xx \\forall z \\forall y \\forall x (z<=x-y <- ((xx<=x & y<=Y) & z<=xx-Y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=* down".
    *    h()<=f()*g()<- (((ff()<=f() & f()<=F()) & (gg()<=g() & g()<=G())) & (h()<=ff()*gg() & h()<=ff()*G() & h()<=F()*gg() & h()<=F()*G()))
    * End.
    * }}}
    */
  @Axiom("<=*", "intervalDownTimes", key = 1::Nil, recursor = (0::0::0::Nil)::(0::0::1::Nil)::(0::1::0::Nil)::(0::1::1::Nil)::Nil)
  lazy val intervalDownTimes = derivedAxiom("<=* down", Sequent(IndexedSeq(), IndexedSeq("h_()<=f_()*g_()<- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & (h_()<=ff_()*gg_() & h_()<=ff_()*G_() & h_()<=F_()*gg_() & h_()<=F_()*G_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (z<=x*y<- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & (z<=xx*yy & z<=xx*Y & z<=X*yy & z<=X*Y)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=1Div down".
    *    h()<=1/f() <- ((f()<=F() & F()*f()>0) & (h()<=1/F()))
    * End.
    * }}}
    */
  @Axiom("<=1/", "intervalDown1Divide")
  lazy val intervalDown1Divide = derivedAxiom("<=1Div down", Sequent(IndexedSeq(), IndexedSeq("h_()<=1/f_() <- ((f_()<=F_() & F_()*f_()>0) & (h_()<=1/F_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "y".asVariable), ("F_()".asTerm, "X".asVariable))(1) &
      byUS(proveBy("\\forall X \\forall y \\forall x (y<=1/x <- ((x<=X & X*x>0) & (y<=1/X)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=Div down".
    *    h() <= f()/g() <- ((ff()<=f() & f()<=F() & gg()<=g() & g()<=G()) & ((G()<0 | 0 < gg()) & (ff()/gg()<=h() & ff()/G()<=h() & F()/gg()<=h() & F()/G()<=h())))
    * End.
    * }}}
    */

//  lazy val intervalDownDivide = derivedAxiom("<=Div down", Sequent(IndexedSeq(), IndexedSeq(("h_() <= f_()/g_() <- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & ((G_()<0 | 0 < gg_()) & (h_()<=ff_()/gg_() & h_()<=ff_()/G_() & h_()<=F_()/gg_() & h_()<=F_()/G_())))").asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
//      byUS(proveBy("\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (z<=x/y <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & ((Y<0|0<yy) &(z<=xx/yy & z<=xx/Y & z<=X/yy & z<=X/Y))))".asFormula, TactixLibrary.RCF))
//  )

  /**
    * {{{Axiom "<=pow down".
    *    h()<=f()^2 <- ((ff()<=f() & f()<=F()) & ((0<= ff_() & h()<=ff()^2) | (F_() <0 & h()<=F()^2)))
    * End.
    * }}}
    */

  @Axiom("<=pow", "intervalDownPower", key = 1::Nil, recursor = (0::0::Nil)::(0::1::Nil)::Nil)
  lazy val intervalDownPower = derivedAxiom("<=pow down", Sequent(IndexedSeq(), IndexedSeq("h_() <= f_()^2 <- ((ff_()<=f_() & f_()<=F_()) & ((0<= ff_() & h_() <= ff_()^2) | (F_()<=0 & h_() <= F_()^2)))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("ff_()".asTerm, "xx".asVariable))(1) &
      byUS(proveBy("\\forall xx \\forall X \\forall z \\forall x (z<=x^2 <- ((xx<=x & x<=X) & ((0 <= xx & z<=xx^2) | (X<= 0 & z<=X^2))))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "dgZeroEquilibrium".
    *   x=0 & n>0 -> [{x'=c*x^n}]x=0
    * End.
    * }}}
    */
  //@note not derivable with Z3; added to AxiomBase and tested to be derivable in DerivedAxiomsTests.
//  lazy val dgZeroEquilibrium = derivedAxiom("dgZeroEquilibrium", Sequent(IndexedSeq(), IndexedSeq("x=0 & n>0 -> [{x'=c*x^n}]x=0".asFormula)),
//    implyR(1) & DA("y' = ( (-c*x^(n-1)) / 2)*y".asDifferentialProgram, "x*y^2=0&y>0".asFormula)(1) <(
//      TactixLibrary.QE,
//      implyR(1) & TactixLibrary.boxAnd(1) & andR(1) <(
//        DifferentialTactics.diffInd()(1) & QE,
//        DA("z' = (c*x^(n-1)/4) * z".asDifferentialProgram, "y*z^2 = 1".asFormula)(1) <(
//          QE,
//          implyR(1) & diffInd()(1) & QE
//        )
//      )
//    )
//  )

  // Metric Normal Form

  /**
    * {{{Axiom "= expand".
    *   f_()=g_() <-> f_()<=g_()&g_()<=f_()
    * End.
    * }}}
    */
  @Axiom("equalExpand", "equalExpand")
  lazy val equalExpand: Lemma = derivedAxiom("= expand", Sequent(IndexedSeq(), IndexedSeq("f_()=g_() <-> f_()<=g_()&g_()<=f_()".asFormula)), QE & done)

  /**
    * {{{Axiom "!= expand".
    *   f_()!=g_() <-> f_()<g_()|g_()<f_()
    * End.
    * }}}
    */
  @Axiom("notEqualExpand", "notEqualExpand")
  lazy val notEqualExpand: Lemma = derivedAxiom("!= expand", Sequent(IndexedSeq(), IndexedSeq("f_()!=g_() <-> f_()<g_()|g_()<f_()".asFormula)), QE & done)


  /**
    * {{{Axiom "<= to <".
    *   f_()<=0 <- f_()<0
    * End.
    * }}}
    */
  @Axiom("leApprox", "leApprox", unifier = "linear", key = 1::Nil, recursor = Nil)
  lazy val le2l: Lemma = derivedAxiom("<= to <", Sequent(IndexedSeq(), IndexedSeq("f_()<=0 <- f_()<0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric <".
    *   f_()<g_() <-> f_()-g_()<0
    * End.
    * }}}
    */
  @Axiom("metricLt", "metricLt", key = 0::Nil, recursor = Nil)
  lazy val metricLess: Lemma = derivedAxiom("metric <", Sequent(IndexedSeq(), IndexedSeq("f_()<g_() <-> f_()-g_()<0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric <=".
    *   f_()<=g_() <-> f_()-g_()<=0
    * End.
    * }}}
    */
  @Axiom("metricLe", "metricLe", key = 0::Nil, recursor = Nil)
  lazy val metricLessEqual: Lemma = derivedAxiom("metric <=", Sequent(IndexedSeq(), IndexedSeq("f_()<=g_() <-> f_()-g_()<=0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric <= & <=".
    *   f_()<=0 & g_()<=0 <-> max(f_(), g_())<=0
    * End.
    * }}}
    */
  @Axiom("metricAndLe", "metricAndLe", key = 0::Nil, recursor = Nil)
  lazy val metricAndLe: Lemma = derivedAxiom("metric <= & <=", Sequent(IndexedSeq(), IndexedSeq("f_()<=0 & g_()<=0 <-> max(f_(), g_())<=0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric < & <".
    *   f_()<0 & g_()<0 <-> max(f_(), g_())<0
    * End.
    * }}}
    */
  @Axiom("metricAndLt", "metricAndLt", key = 0::Nil, recursor = Nil)
  lazy val metricAndLt: Lemma = derivedAxiom("metric < & <", Sequent(IndexedSeq(), IndexedSeq("f_()<0 & g_()<0 <-> max(f_(), g_())<0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric <= | <=".
    *   f_()<=0 | g_()<=0 <-> min(f_(), g_())<=0
    * End.
    * }}}
    */
  @Axiom("metricOrLe", "metricOrLe", key = 0::Nil, recursor = Nil)
  lazy val metricOrLe: Lemma = derivedAxiom("metric <= | <=", Sequent(IndexedSeq(), IndexedSeq("f_()<=0 | g_()<=0 <-> min(f_(), g_())<=0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric < | <".
    *   f_()<0 | g_()<0 <-> min(f_(), g_())<0
    * End.
    * }}}
    */
  @Axiom("metric < | <", "metricOrLt", "metricOrLt", key = 0::Nil, recursor = Nil)
  lazy val metricOrLt: Lemma = derivedAxiom("metric < | <", Sequent(IndexedSeq(), IndexedSeq("f_()<0 | g_()<0 <-> min(f_(), g_())<0".asFormula)), QE & done)

  //Extra arithmetic axioms for SimplifierV3 not already included above

  /**
    * {{{Axiom "* identity neg".
    *    f()*-1 = -f()
    * End.
    * }}}
    */
  @Axiom("timesIdentityNeg", "timesIdentityNeg")
  lazy val timesIdentityNeg =
    derivedAxiom("* identity neg", Sequent(IndexedSeq(), IndexedSeq("f_()*-1 = -f_()".asFormula)),
      allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
        byUS(proveBy("\\forall x (x*-1 = -x)".asFormula, TactixLibrary.RCF))
    )

  /**
    * {{{Axiom "-0".
    *    (f()-0) = f()
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("minusZero", unifier = "linear")
  lazy val minusZero = derivedAxiom("-0", Sequent(IndexedSeq(), IndexedSeq("(f_()-0) = f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (x-0 = x)".asFormula, TactixLibrary.RCF)))

  /**
    * {{{Axiom "0-".
    *    (0-f()) = -f()
    * End.
    * }}}
    *
    * @Derived
    */
  @Axiom("zeroMinus", unifier = "linear")
  lazy val zeroMinus = derivedAxiom("0-", Sequent(IndexedSeq(), IndexedSeq("(0-f_()) = -f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (0-x = -x)".asFormula, TactixLibrary.RCF)))

  //TODO: add more text to the following
  @Axiom("gtzImpNez" , "gtzImpNez")
  lazy val gtzImpNez = derivedAxiom(">0 -> !=0", Sequent(IndexedSeq(), IndexedSeq("f_() > 0 -> f_()!=0".asFormula)), QE)
  @Axiom("ltzImpNez" , "ltzImpNez")
  lazy val ltzImpNez = derivedAxiom("<0 -> !=0", Sequent(IndexedSeq(), IndexedSeq("f_() < 0 -> f_()!=0".asFormula)), QE)

  @Axiom("zeroDivNez", "zeroDivNez")
  lazy val zeroDivNez = derivedAxiom("!=0 -> 0/F", Sequent(IndexedSeq(), IndexedSeq("f_() != 0 -> 0/f_() = 0".asFormula)), QE)
  @Axiom("powZero", "powZero")
  lazy val powZero = derivedAxiom("F^0", Sequent(IndexedSeq(), IndexedSeq("f_()^0 = 1".asFormula)), QE)
  @Axiom("powOne" , "powOne")
  lazy val powOne = derivedAxiom("F^1", Sequent(IndexedSeq(), IndexedSeq("f_()^1 = f_()".asFormula)), QE)

  private def equivSequent(t: String, tt: String): Sequent =
    Sequent(IndexedSeq(),IndexedSeq(Equiv(t.asFormula,tt.asFormula)))
  private def implySequent(f: String, t: String, tt: String): Sequent =
    Sequent(IndexedSeq(),IndexedSeq(Imply(f.asFormula,Equiv(t.asFormula,tt.asFormula))))
  private def propQE: BelleExpr = prop & QE & done
  // The following may already appear above
  // They are stated here in a shape suitable for the simplifier
  //(Ir)reflexivity axioms for comparison operators
  @Axiom("lessNotRefl", "lessNotRefl", unifier = "full")
  lazy val lessNotRefl      = derivedAxiom("< irrefl", equivSequent("F_()<F_()","false"), propQE)
  @Axiom("greaterNotRefl", "greaterNotRefl", unifier = "full")
  lazy val greaterNotRefl   = derivedAxiom("> irrefl", equivSequent("F_()>F_()","false"), propQE)
  @Axiom("notEqualNotRefl", "notEqualNotRefl", unifier = "full")
  lazy val notEqualNotRefl  = derivedAxiom("!= irrefl", equivSequent("F_()!=F_()","false"), propQE)
  /** @see [[equivReflexiveAxiom]] */
  @Axiom("equalRefl", "equalRefl", unifier = "full")
  lazy val equalRefl        = derivedAxiom("= refl", equivSequent("F_() = F_()","true"), propQE)
  @Axiom("lessEqualRefl", "lessEqualRefl", unifier = "full")
  lazy val lessEqualRefl    = derivedAxiom("<= refl", equivSequent("F_() <= F_()","true"), propQE)
  @Axiom("greaterEqualRefl", "greaterEqualRefl", unifier = "full")
  lazy val greaterEqualRefl = derivedAxiom(">= refl", equivSequent("F_() >= F_()","true"), propQE)

  //(anti) symmetry axioms
  @Axiom("equalSym", "equalSym")
  lazy val equalSym = derivedAxiom("= sym", implySequent("F_() = G_()", "G_() = F_()","true"), propQE)
  @Axiom("notEqualSym", "notEqualSym")
  lazy val notEqualSym = derivedAxiom("!= sym", implySequent("F_() != G_()","G_() != F_()","true"), propQE)
  @Axiom("greaterNotSym", "greaterNotSym")
  lazy val greaterNotSym = derivedAxiom("> antisym", implySequent("F_() > G_()","G_() > F_()","false"), propQE)
  @Axiom("lessNotSym", "lessNotSym")
  lazy val lessNotSym = derivedAxiom("< antisym", implySequent("F_() < G_()","G_() < F_()","false"), propQE)


  /**
    * {{{Axiom "all stutter".
    *    \forall x p <-> \forall x p
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */
  @Axiom("all stutter", "allStutter", key = 0::Nil, recursor = Nil)
  lazy val forallStutter: Lemma = derivedAxiom("all stutter",
    Sequent(IndexedSeq(), IndexedSeq("\\forall x_ p_(x_) <-> \\forall x_ p_(x_)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "exists stutter".
    *    \exists x p <-> \exists x p
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */
  @Axiom("exists stutter", "existsStutter", key = 0::Nil, recursor = Nil)
  lazy val existsStutter: Lemma = derivedAxiom("exists stutter",
    Sequent(IndexedSeq(), IndexedSeq("\\exists x_ p_(x_) <-> \\exists x_ p_(x_)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  // Liveness additions

  /**
    * {{{Axiom "K<&>".
    *    [{c & q(||) & !p(||)}]!r(||) -> (<{c & q(||)}>r(||) -> <{c & q(||)}>p(||))
    * End.
    * }}}
    *
    * @Derived
    * @note postcondition refinement
    */
  @Axiom("KDomD", "KDomD")
  lazy val kDomD: Lemma =
    derivedAxiom("K<&>",
      "==> [{c & q(||) & !p(||)}]!r(||) -> (<{c & q(||)}>r(||) -> <{c & q(||)}>p(||))".asSequent,
      implyR(1) & implyR(1) &
        useExpansionAt("<> diamond")(1) &
        useExpansionAt("<> diamond")(-2) &
        notL(-2) & notR(1) & implyRi()(-1,1) &
        useAt(DiffRefine, PosInExpr(1::Nil))(1) & TactixLibrary.boxAnd(1) & andR(1) <(
        DW(1) & G(1) & implyR(1) & closeId,
        closeId
      )
    )
}
