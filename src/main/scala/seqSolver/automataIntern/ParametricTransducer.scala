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
import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}

object ParametricTransducer {

  private def toSFT(transducer: Transducer) : SFT[Conjunction, ITerm, ITerm] = transducer match {
    case that : ParametricTransducer => that.underlying
    case _ => throw new IllegalArgumentException
  }

}

class ParametricTransducer(val underlying : SFT[Conjunction, ITerm, ITerm], pt : ParameterTheory) extends Transducer {
  override def toString: String = underlying.toString


  override def preImage(aut: Automaton): Automaton = {
    // TODO build automata with internal state
    new automataIntern.ParametricAutomaton(underlying.inverseImage(ParametricAutomaton.toSFA(aut), pt), pt)
  }

  def apply(input : Seq[ITerm]): Option[Seq[ITerm]] = {
    val l = underlying.outputOn(input.asJava, pt).asScala
    // TODO l can be Null
    if (l.isEmpty){
      None
    }
    else
      Some(l)
  }

}

class ParametricTransducerBuilder(val parameterTheory: ParameterTheory) {

  var stateCounter = 0
  var acceptingStates : MHashSet[Integer] = MHashSet[Integer]()
  var initialState = 0

  def getInitialState : Int = initialState

  def getNewState : Int = {stateCounter += 1; stateCounter -1}

  def setAccept(q : Int, b : Boolean) : Unit = {
    if (b) {
      acceptingStates += q
    }
    else {
      acceptingStates -= q
    }
  }
}
