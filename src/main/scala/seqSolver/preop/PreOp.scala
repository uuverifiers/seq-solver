package seqSolver.preop

import ap.parser.ITerm
import ap.terfor.conjunctions.Conjunction
import automata.sfa.SFA
import seqSolver.ParameterTheory

trait PreOp {

  def apply(argumentConstraints : Seq[Seq[SFA[Conjunction, ITerm]]],
            resultConstraint: SFA[Conjunction, ITerm], pt : ParameterTheory) : Iterator[Seq[SFA[Conjunction, ITerm]]]

}
