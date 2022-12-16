package seqSolver.preop

import ap.parser.ITerm
import ap.terfor.conjunctions.Conjunction
import automata.sfa.SFA
import seqSolver.ParameterTheory

trait PreOp {

  def apply(resultConstraint: SFA[Conjunction, ITerm], pt : ParameterTheory) : Iterator[Seq[SFA[Conjunction, ITerm]]]

}
