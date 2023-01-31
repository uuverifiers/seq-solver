package seqSolver.automataIntern

import ap.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
import ap.parser.{ConstantSubstVisitor, ITerm}
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Conjunction
import ap.terfor.substitutions.ConstantSubst
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

  override def postImage: Automaton = {
    new ParametricAutomaton(underlying.getOutputSFA(pt),pt)
  }

  def apply(input : Seq[ITerm], prover : SimpleAPI): Option[Seq[ITerm]] = {
    val l = getOutput(input, prover)
    l
  }

  def getOutput(input : Seq[ITerm], prover : SimpleAPI) : Option[Seq[ITerm]] = {
    if(underlying.isEpsilonFree){
      return getOutputRec(input, prover, underlying.getInitialState)
    }
    else{
      throw new Exception("Transducer is not epsilon free")
    }
  }

  def getOutputRec(input : Seq[ITerm], prover: ap.SimpleAPI, currentState : Int) : Option[Seq[ITerm]] = {
    import ap.parser.IExpression._
    println("test1")
    if (input.isEmpty){
      if (underlying.isFinalState(currentState)){
        return Some(Seq())
      }
      else{
        return None
      }
    }
    else {
      val currentLetter = input.head
      val allSuccessors = underlying.getInputMovesFrom(currentState)
      for (successor <- allSuccessors.asScala){
        prover.scope{
          val new_const = pt.charSort newConstant ("l")
          prover.addConstant(new_const)
          val z = ConstantSubst(pt.charSymbol, new_const, prover.order)(successor.guard)
          prover.addAssertion(z)
          prover.addAssertion(new_const === currentLetter)
          if (prover.??? == ProverStatus.Sat) {
            val _tmp = getOutputRec(input.tail, prover, successor.to)
            if (_tmp.nonEmpty){
              if (successor.outputFunctions.isEmpty){
                return Some(_tmp.get)
              }
              else{
                val l = new MHashMap[ConstantTerm, ITerm]
                l.put(pt.charSymbol, new_const)
                val t = ConstantSubstVisitor(successor.outputFunctions.get(0), l)
                return Some(Seq(prover.evalToTerm(t)) ++ _tmp.get)

              }
            }
            else{
              // do nothing
            }

          }
        }
      }
      return None
    }
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
