package seqSolver.automataIntern

import ap.api.SimpleAPI
import ap.parser.ITerm

trait Automaton {
  /**
   * Union
   */
  def |(that : Automaton) : Automaton

  /**
   * Intersection
   */
  def &(that : Automaton) : Automaton

  /**
   * Complementation
   */
  def unary_! : Automaton

  /**
   * Check whether the automaton accepts a given word.
   */
  def apply(word : Seq[ITerm], prover : SimpleAPI) : Boolean

  def isEmpty : Boolean
  /*
    /**
     * Check whether this automaton accepts any word.
     */
    def isEmpty : Boolean

    /**
     * Check whether the automaton accepts a given word.
     */
    def apply(word : Seq[Int]) : Boolean

    /**
     * Get any word accepted by this automaton, or <code>None</code>
     * if the language is empty
     */
    def getAcceptedWord : Option[Seq[Int]]*/

}
