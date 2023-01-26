package seqSolver.preop
import ap.parser.ITerm
import seqSolver.SeqTheory
import seqSolver.automataIntern.ParametricAutomaton.reverseAut
import seqSolver.automataIntern.{Automaton, ParametricAutomaton}

object ReversePreOp extends PreOp {
  override def apply(resultConstraint: Automaton, seqTheory: SeqTheory): Iterator[Seq[Automaton]] = resultConstraint match {
    case resultConstraint : ParametricAutomaton => {
      (Iterator(Seq(reverseAut(resultConstraint))))
    }
    case _ =>
      throw new IllegalArgumentException

  }

  override def eval(arguments: Seq[Seq[ITerm]]): Option[Seq[ITerm]] = {

    Some(arguments(0).reverse)
  }

  override def toString = "Reverse"
}
