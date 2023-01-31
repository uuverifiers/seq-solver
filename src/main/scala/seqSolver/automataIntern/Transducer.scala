package seqSolver.automataIntern

import ap.SimpleAPI
import ap.parser.ITerm

trait Transducer {
  def apply(arg: Seq[ITerm], prover : SimpleAPI): Option[Seq[ITerm]]


  def preImage(aut : Automaton) : Automaton

  def postImage : Automaton

}
