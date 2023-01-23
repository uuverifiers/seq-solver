package seqSolver.preop

import ap.parser.ITerm
import seqSolver.SeqTheory
import seqSolver.automataIntern.{Automaton, Transducer}

object TransducerPreOp {
  def apply(t : Transducer) = new TransducerPreOp(t)

}

class TransducerPreOp(t : Transducer) extends PreOp {
  override def apply(resultConstraint: Automaton, seqTheory: SeqTheory): Iterator[Seq[Automaton]] = {
    (Iterator(Seq(t.preImage(resultConstraint))))
  }

  override def eval(arguments: Seq[Seq[ITerm]]): Option[Seq[ITerm]] = {
    assert (arguments.size == 1)
    val arg = arguments(0)
    t(arg)
  }
}
