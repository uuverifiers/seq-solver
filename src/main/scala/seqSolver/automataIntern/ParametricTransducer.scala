package seqSolver.automataIntern

import ap.parser.ITerm
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Conjunction
import seqSolver.{ParameterTheory, automataIntern}
import java.util
import scala.collection.mutable
import scala.collection.JavaConverters._
import scala.collection.mutable.ListBuffer
import transducers.sft.SFT

object ParametricTransducer {

  private def toSFT(transducer: Transducer) : SFT[Conjunction, ConstantTerm, ITerm] = transducer match {
    case that : ParametricTransducer => that.underlying
    case _ => throw new IllegalArgumentException
  }

}

class ParametricTransducer(val underlying : SFT[Conjunction, ConstantTerm, ITerm], pt : ParameterTheory) extends Transducer {
  override def toString: String = underlying.toString

  override def preImage(aut: Automaton): Automaton = new automataIntern.ParametricAutomaton(underlying.inverseImage(ParametricAutomaton.toSFA(aut), pt), pt)

  def apply(input : Seq[ITerm]): Option[Seq[ITerm]] = {
    val l = underlying.outputOn(input.asJava, pt).asScala
    if (l.isEmpty){
      None
    }
    else
      Some(l)
  }

}
