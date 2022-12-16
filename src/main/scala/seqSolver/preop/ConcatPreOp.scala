package seqSolver.preop

import ap.parser.ITerm
import ap.terfor.conjunctions.Conjunction
import automata.sfa.SFA
import seqSolver.ParameterTheory

import scala.collection.JavaConverters._

object ConcatPreOp extends PreOp {
  def apply(resultConstraint: SFA[Conjunction, ITerm], pt : ParameterTheory) : Iterator[Seq[SFA[Conjunction, ITerm]]] =  {
    (for (s <- resultConstraint.getStates.asScala) yield {
      List(SFA.MkSFA(resultConstraint.getTransitions, resultConstraint.getInitialState, List(new Integer(s)).asJava, pt)
        , SFA.MkSFA(resultConstraint.getTransitions, new Integer(s), resultConstraint.getFinalStates, pt)
        )
    }).iterator
  }
}
