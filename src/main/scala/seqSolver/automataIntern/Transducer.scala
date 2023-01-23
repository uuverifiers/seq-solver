package seqSolver.automataIntern

import ap.parser.ITerm

trait Transducer {
  def apply(arg: Seq[ITerm]): Option[Seq[ITerm]]


  def preImage(aut : Automaton) : Automaton

}
