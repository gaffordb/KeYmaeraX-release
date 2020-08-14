package edu.cmu.cs.ls.keymaerax.cli

import spray.json._

/** Extracts submission information from a JSON AST.  */
object Submission {

  private val CHILDREN = "children"
  private val POINT_VALUE = "point_value"
  private val TITLE = "title"
  private val ID = "id"
  private val LABEL = "label"
  private val NAME = "name"
  private val TYPE = "type"
  private val BODY = "body"
  private val IS_CHOICE = "is_choice"
  private val IS_FILL_IN_GAP = "is_fill_in_the_gap"
  private val IS_SELECTED = "is_selected"
  private val PROMPTS = "prompts"

  trait Answer {
    val id: Long
    val text: String
  }
  case class TextAnswer(id: Long, text: String) extends Answer
  case class ChoiceAnswer(id: Long, text: String, isSelected: Boolean) extends Answer
  /** A single quiz question with submitted answer. */
  case class Prompt(id: Long, points: Double, answers: List[Answer])
  /** A problem segment. */
  case class Problem(id: Long, title: String, prompts: List[Prompt])
  /** A quiz chapter. */
  case class Chapter(id: Long, label: String, problems: List[Problem])

  def extract(root: JsObject): Chapter = {
    val id = root.fields(ID) match { case JsNumber(n) => n.toLong }
    val label = root.fields(LABEL) match { case JsString(s) => s }
    val problems = extractProblems(root)
    Chapter(id, label, problems)
  }

  def extractProblems(root: JsObject): List[Problem] = {
    root.fields.get(CHILDREN) match {
      case Some(JsArray(segments)) =>
        segments.flatMap({
          case s: JsObject =>
            //@note only auto-grade those segments that are worth points
            s.fields.get(POINT_VALUE) match {
              case Some(JsNumber(n)) if n>0 => s.fields.get(TYPE) match {
                case Some(JsString("segment")) => extractProblems(s)
                case Some(JsString("atom")) => s.fields(NAME) match {
                  case JsString("problem") => Some(extractProblem(s))
                  case _ => None
                }
                case _ => None
              }
              case _ => None
            }
          case _ => None
        }).toList
      case _ => List.empty
    }
  }

  /** Extracts a problem segment from the `root` JSON problem object (identified by having "name"="problem"). */
  private def extractProblem(root: JsObject): Problem = {
    require(root.fields(NAME) match { case JsString("problem") => true case _ => false })
    val id = root.fields(ID) match { case JsNumber(n) => n.toLong }
    val title = root.fields(TITLE) match { case JsString(s) => s }
    val prompts = root.fields.get(PROMPTS) match {
      case Some(JsArray(prompts)) => prompts.map(_.asJsObject).map(extractPrompt).toList
      case _ => List.empty
    }
    Problem(id, title, prompts)
  }

  /** Extracts a prompt and the answers submitted in response to it. */
  private def extractPrompt(root: JsObject): Prompt = {
    val id = root.fields(ID) match { case JsNumber(n) => n.toLong }
    val points = root.fields(POINT_VALUE) match { case JsNumber(n) => n.toDouble }
    val answers = root.fields(CHILDREN) match {
      case JsArray(s) =>
        s.map(sub => {
          val fields = sub.asJsObject.fields
          val id = fields(ID) match { case JsNumber(n) => n.toLong }
          (fields.get(IS_CHOICE), fields.get(IS_FILL_IN_GAP)) match {
            case (Some(JsBoolean(true)), None | Some(JsBoolean(false))) =>
              val text = fields(BODY) match { case JsString(s) => s }
              //@todo assumes selected option will be marked
              val answer = fields(IS_SELECTED) match {
                case JsBoolean(b) => b
              }
              ChoiceAnswer(id, text, answer)
            case (None | Some(JsBoolean(false)), None | Some(JsBoolean(_))) =>
              //@todo assumes submission will be in the prompt body
              val answer = fields(BODY) match {
                case JsString(s) => s
              }
              TextAnswer(id, answer)
          }
        }).toList
      case _ => List.empty
    }
    Prompt(id, points, answers)
  }

}
