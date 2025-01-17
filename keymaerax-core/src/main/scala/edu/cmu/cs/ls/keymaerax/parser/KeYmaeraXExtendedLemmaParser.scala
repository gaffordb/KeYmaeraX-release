/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.core.{Formula, Provable, Sequent}
import edu.cmu.cs.ls.keymaerax.lemma.Evidence
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.TokenStream
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

import scala.annotation.tailrec
import scala.collection.immutable

/**
  * Parses lemma string representations from the following lemma format:
  * {{{
  *   Lemma "<<lemmaname>>".
  *     "<<Provable.toStorageString(fact.underlyingProvable)"
  *   End.
  *   Tool.
  *     <<key>> """"<<value>>""""
  *     ...
  *   End.
  * }}}
  *
  * Created by smitsch on 7/03/15.
  * Modified by nfulton on 12/16/15 -- Lemmas are now more general.
  * @author Stefan Mitsch
  * @author Nathan Fulton
  */
object KeYmaeraXExtendedLemmaParser extends (String => (Option[String], Provable, Sequent, immutable.List[Evidence]))
  with Logging {
  /** The lemma name, provable, and the supporting evidence */
  private type Lemma = (Option[String], Provable, Sequent, List[Evidence])

  /**
    * Returns the lemma parsed from `inputWithPossibleBOM` after removing the BOM.
    * @param inputWithPossibleBOM The contents of the lemma file.
    * @return A lemma, with tool evidence (tool input/output) as occurring in the file.
    */
  def apply(inputWithPossibleBOM: String): Lemma = try {
    //@todo sort checking
    val input = ParserHelper.removeBOM(inputWithPossibleBOM)
    val tokens = KeYmaeraXLexer.inMode(input, LemmaFileMode)
    logger.debug("Tokens are: " + tokens)
    parseLemma(tokens)
  } catch {
    case e: ParseException => throw e.inContext("input:  " + inputWithPossibleBOM)
    case e: IllegalArgumentException => throw ParseException("Illegal argument", e).inInput(inputWithPossibleBOM)
  }

  /**
    * Parses the token stream `input` into a lemma.
    * @param input Token string for the lemma file.
    * @return A lemma (name, associated formula, and evidence).
    */
  def parseLemma(input: TokenStream): Lemma = {
    require(input.last.tok == EOF, "Token streams have to end in " + EOF)
    require(input.head.tok.equals(LEMMA_BEGIN), "Expected ALP file to begin with Lemma block but found " + input.head)
    val (nextLemma, nextFormula, nextMinSequent, nextEvidence, remainder) = parseNextLemma(input)
    if (remainder.length == 1 && remainder.head.tok.equals(EOF)) (nextLemma, nextFormula, nextMinSequent, nextEvidence)
    else throw new IllegalArgumentException("Expected only one lemma")
  }

  def parseProvableSig(input: TokenStream): (String, String, TokenStream) = {
    val (Token(DOUBLE_QUOTES_STRING(storedProvableInternal), _) :: Token(DOUBLE_QUOTES_STRING(storedMinSeqInternal), _) :: Nil, remainderTokensInternal) = input.span(_.tok != END_BLOCK) match {
      case (Token(PERIOD, _) :: a, Token(END_BLOCK, _) :: Token(PERIOD, _) :: r) => (a, r)
      case (a, Token(END_BLOCK, _) :: Token(PERIOD, _) :: r) => (a, r)
      case (a, Token(END_BLOCK, _) :: r) => (a, r)
    }
    (storedProvableInternal, storedMinSeqInternal, remainderTokensInternal)
  }
  def parseProvableSigOld(input: TokenStream): (String, String, TokenStream) = {
    val (Token(DOUBLE_QUOTES_STRING(storedProvableInternal), _) :: Nil, remainderTokensInternal) = input.span(_.tok != END_BLOCK) match {
      case (Token(PERIOD, _) :: a, Token(END_BLOCK, _) :: Token(PERIOD, _) :: r) => (a, r)
      case (a, Token(END_BLOCK, _) :: Token(PERIOD, _) :: r) => (a, r)
      case (a, Token(END_BLOCK, _) :: r) => (a, r)
    }
    (storedProvableInternal, "", remainderTokensInternal)
  }

  /** Parses the next lemma from token stream `input` and returns the lemma as well as the remaining tokens. */
  def parseNextLemma(input: TokenStream): (Option[String], Provable, Sequent, List[Evidence], TokenStream) = {
    require(input.head.tok == LEMMA_BEGIN, "Expected ALP file to begin with Lemma block")

    val (name, nameRemainderTokens) = parseLemmaName(input)
    //val (storedProvable, remainderTokens) = parseProvable(nameRemainderTokens)
    val (storedProvable, storedMinSeq, remainderTokens) = try { parseProvableSigOld(nameRemainderTokens)} catch {case _ => parseProvableSig(nameRemainderTokens)}

    var minSeq = Sequent(immutable.IndexedSeq(), immutable.IndexedSeq())

    val (allEvidence, remainder) = parseAllEvidence(remainderTokens)
    val provable = Provable.fromStorageString(storedProvable)


    if (!storedMinSeq.isEmpty) {
      val msinput = ParserHelper.removeBOM(storedMinSeq)
      val mstokens = KeYmaeraXLexer.inMode(msinput, LemmaFileMode)
      minSeq = edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXStoredProvableParser.parseSequent(mstokens)
    }

    (name, provable, minSeq, allEvidence, remainder)
  }

  /** Parses the lemma name. Returns the lemma name (None if empty) and the token remainders. */
  private def parseLemmaName(input: TokenStream): (Option[String], TokenStream) = {
    require(input.tail.head.tok.isInstanceOf[DOUBLE_QUOTES_STRING], "Expected ALP block to have a string as a name")
    input match {
      case Token(LEMMA_BEGIN, _) :: Token(DOUBLE_QUOTES_STRING(x), _) :: r => if (x.nonEmpty) (Some(x), r) else (None, r)
      case _ => throw new AssertionError("Expected ALP block to have a string as a name") // duplicate requirement
    }
  }

  /**
    * Parses token stream `input` into a list of evidence. Returns the evidence and the remainder tokens.
    * @param input Token string for the lemma file.
    * @return A list of evidence (tool input/output) and the remainder tokens.
    */
  @tailrec
  def parseAllEvidence(input: TokenStream, prevEvidence: List[Evidence] = Nil): (List[Evidence], TokenStream) = {
    require(input.last.tok == EOF, "Token streams have to end in " + EOF)
    if (input.head.tok == EOF) (prevEvidence, input)
    else {
      val (evidence, remainder) = parseNextEvidence(input)
      if (remainder.length == 1 && remainder.head.tok.equals(EOF)) (prevEvidence :+ evidence, remainder)
      else parseAllEvidence(remainder, prevEvidence :+ evidence)
    }
  }

  /** Parses token stream `input` into a single piece of evidence; returns the evidence and the remainder tokens. */
  def parseNextEvidence(input: TokenStream): (Evidence, TokenStream) = {
    require(input.head.tok == TOOL_BEGIN, s"expected to find a begin evidence block but found ${input.head.tok}")

    //Find the End. token and exclude it.
    val (toolTokens, remainderTokens) =
      //1st element is TOOL_BEGIN, 2nd is a tool evidence key.
      input.tail.tail.span(_.tok != END_BLOCK) match {
        case (Token(PERIOD, _) :: a, Token(END_BLOCK, _) :: Token(PERIOD, _) :: r) => (a, r)
        case (a, Token(END_BLOCK, _) :: Token(PERIOD, _) :: r) => (a, r)
        case (a, Token(END_BLOCK, _) :: r) => (a, r)
      }

    val evidenceLines = parseEvidenceLines(toolTokens)

    val evidence = input.head.tok match {
      case TOOL_BEGIN => ToolEvidence(evidenceLines)
    }

    (evidence, remainderTokens)
  }

  def parseEvidenceLines(input: TokenStream): immutable.List[(String, String)] = {
    require(input.head.tok match { case IDENT(_, _) => true case _ => false }, "expected to begin with key.")
    require(input.tail.head.tok match { case TOOL_VALUE(_) => true case _ => false }, "expected actual value.")

    var evidence = immutable.List[(String, String)]()
    var line = input

    while (line.nonEmpty &&
      (line.head.tok match { case IDENT(_, _) => true case _ => false }) &&
      (line.tail.head.tok match { case TOOL_VALUE(_) => true case _ => false })) {
      val key = line.head match {
        case Token(IDENT(x, None),_) => x
        case Token(IDENT(x, Some(i)),_) => x + "_" + i
        case _ => throw new AssertionError("Require should have failed.")
      }

      val value = line.tail.head match {
        case Token(TOOL_VALUE(x),_) => x
        case _ => throw new AssertionError("Require should have failed.")
      }

      evidence = evidence :+ (key -> value)
      line = line.tail.tail
    }

    evidence
  }

}
