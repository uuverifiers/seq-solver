package seqSolver.automataIntern

import ap.api.SimpleAPI
import ap.parser.ITerm
import ap.terfor.conjunctions.Conjunction
import ap.types.Sort
import automata.sfa.{SFA, SFAInputMove, SFAMove}
import seqSolver.{ParameterTheory, SFAUtilities, SeqTheory, automataIntern}
import seqSolver.automataIntern.ParametricAutomaton.toSFA

import java.util
import scala.collection.mutable
import scala.collection.JavaConverters._
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}



object ParametricAutomaton {
  private def toSFA(aut : Automaton) : SFA[Conjunction, ITerm] = aut match {
    case that : ParametricAutomaton => that.underlying
    case _ =>
      throw new IllegalArgumentException
  }



  def makeUniversal(seqTheory : SeqTheory) : ParametricAutomaton = {
    val pt: ParameterTheory = ParameterTheory(seqTheory.sort, List(seqTheory.sort))
    new ParametricAutomaton(SFA.getFullSFA(pt), pt)
  }



}

class ParametricAutomaton(val underlying : SFA[Conjunction,ITerm], pt : ParameterTheory) extends Automaton {

  override def toString: String = underlying.toString

  val sort = pt.charSort
  /**
   * Union
   */
  override def |(that: Automaton): Automaton = new ParametricAutomaton(underlying.unionWith(toSFA(that), pt), pt)

  /**
   * Intersection
   */
  override def &(that: Automaton): Automaton = new ParametricAutomaton(underlying.intersectionWith(toSFA(that), pt), pt)

  /**
   * Complementation
   */
  override def unary_! : Automaton = new ParametricAutomaton(underlying.complement(pt), pt)

  def getSuccessors(s: Integer): Iterable[SFAInputMove[Conjunction, ITerm]] = {
    underlying.getInputMovesFrom(s).asScala
  }

  def isEmpty : Boolean = {
    println("PAut is empty" + underlying.isEmpty)
    underlying.isEmpty
  }

  def apply(word : Seq[ITerm], prover : SimpleAPI) : Boolean = {



    underlying.accepts(word.toList.asJava, pt)
  }

  lazy val initialState : Int = underlying.getInitialState

  lazy val states : Iterable[Integer] = underlying.getStates.asScala

  lazy val acceptingStates : Set[Integer] = underlying.getFinalStates.asScala.toSet

  lazy val transitions : Iterable[SFAMove[Conjunction, ITerm]] = underlying.getTransitions.asScala

}

// TODO list of sort of the parameters
class ParametricAutomatonBuilder(val parameterTheory: ParameterTheory) {

  var stateCounter = 0
  var parameters = 0
  var init = 0
  var acceptingStates: ListBuffer[Integer] = ListBuffer[Integer]()
  val transitions: ListBuffer[SFAMove[Conjunction, ITerm]] = ListBuffer[SFAMove[Conjunction, ITerm]]()

  def setParameters(i : Int): Unit = parameters = i

  def initialState : Int = init

  def getNewState: Int = {stateCounter+= 1; stateCounter-1}

  def setInitialState(q : Int) : Unit = init = q

  def setAccepting(q : Int) : Unit = {acceptingStates += q}

  def addTransition(from : Int, to : Int, guard : Conjunction) : Unit = {
    val l = new SFAInputMove[Conjunction, ITerm](from, to, guard)
    transitions += l
  }

  def setFixedAutomaton(initialState : Int, transitions : util.Collection[SFAMove[Conjunction, ITerm]], accepting : List[Integer]) : ParametricAutomaton = {
    new ParametricAutomaton(SFA.MkSFA(transitions, initialState, accepting.asJava, parameterTheory), parameterTheory)
  }

  def getAutomaton : ParametricAutomaton = {
    new ParametricAutomaton(SFA.MkSFA(transitions.asJava, init, acceptingStates.asJava, parameterTheory), parameterTheory)
  }

  def makeUniversal : ParametricAutomaton = {
    new automataIntern.ParametricAutomaton(SFA.getFullSFA(parameterTheory), parameterTheory)
  }

}
