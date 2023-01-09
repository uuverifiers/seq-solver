package seqSolver.preop

import ap.parser.ITerm
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Conjunction
import automata.sfa.SFA
import seqSolver.{ParameterTheory, SeqTheory}
import seqSolver.automataIntern.Automaton

trait PreOp {

  def apply(resultConstraint: Automaton, seqTheory : SeqTheory) : Iterator[Seq[Automaton]]

  def eval(arguments : Seq[Seq[ITerm]]) : Option[Seq[ITerm]]

}
