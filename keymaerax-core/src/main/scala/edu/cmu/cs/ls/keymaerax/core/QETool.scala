/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-17
  */
package edu.cmu.cs.ls.keymaerax.core

/**
  * Interface to quantifier elimination tools.
  */
trait QETool {
  /**
    * Returns a quantifier-free formula that is equivalent to the specified formula.
    * @param formula The formula whose quantifier-free equivalent is sought.
    * @return An equivalent quantifier-free formula.
    * @requires formula is in first-order real arithmetic
    * @ensures \result is equivalent to formula
    * @ensures \result is quantifier-free
    */
  def quantifierElimination(formula: Formula): Formula
}
