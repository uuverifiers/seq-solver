package seqSolver.preop

import ap.parser.ITerm
import ap.terfor.ConstantTerm
import ap.terfor.TerForConvenience.l
import ap.terfor.conjunctions.Conjunction
import automata.sfa.SFA
import seqSolver.{ParameterTheory, SeqTheory}
import seqSolver.automataIntern.{Automaton, ParametricAutomaton, ParametricAutomatonBuilder}

import scala.collection.JavaConverters._

object ConcatPreOp extends PreOp {
  def apply(resultConstraint: Automaton, seqTheory: SeqTheory) : Iterator[Seq[Automaton]] = resultConstraint match {

    case resultConstraint : ParametricAutomaton => {
      (for (s <- resultConstraint.states) yield {
        val builder = new ParametricAutomatonBuilder(seqTheory.parameterTheory)

        List(builder.setFixedAutomaton(resultConstraint.initialState, resultConstraint.underlying.getTransitions, List(new Integer(s))),
          builder.setFixedAutomaton(s, resultConstraint.underlying.getTransitions, resultConstraint.acceptingStates.toList
        ))
      }).iterator
    }
    case _ => {
      throw new Exception("Not a Parametric Automaton")
    }
  }

  def eval(arguments : Seq[Seq[ITerm]]) : Option[Seq[ITerm]] = {
    Some(arguments.head ++ arguments(1))
  }

}
