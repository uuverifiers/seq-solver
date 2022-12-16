package seqSolver.automataIntern

import ap.parser.ITerm
import ap.terfor.conjunctions.Conjunction
import ap.types.Sort
import automata.sfa.{SFA, SFAInputMove, SFAMove}
import seqSolver.{ParameterTheory, SFAUtilities, automataIntern}
import seqSolver.automataIntern.ParametricAutomaton.toSFA

import scala.collection.mutable
import scala.collection.JavaConverters._
import scala.collection.mutable.ListBuffer

object ParametricAutomaton {
  private def toSFA(aut : Automaton) : SFA[Conjunction, ITerm] = aut match {
    case that : ParametricAutomaton => that.underlying
    case _ =>
      throw new IllegalArgumentException
  }

  def makeUniversal(sort: Sort) : ParametricAutomaton = {
    val pt: ParameterTheory = ParameterTheory(sort, List(sort))
    new ParametricAutomaton(SFA.getFullSFA(pt), pt, 0)
  }

}

class ParametricAutomaton(val underlying : SFA[Conjunction,ITerm], pt : ParameterTheory, val parameters : Int) extends Automaton {
  val parameter: Int = parameters
  val sort = pt.charSort
  /**
   * Union
   */
  override def |(that: Automaton): Automaton = new ParametricAutomaton(underlying.unionWith(toSFA(that), pt), pt, parameters)

  /**
   * Intersection
   */
  override def &(that: Automaton): Automaton = new ParametricAutomaton(underlying.intersectionWith(toSFA(that), pt), pt, parameters)

  /**
   * Complementation
   */
  override def unary_! : Automaton = new ParametricAutomaton(underlying.complement(pt), pt, parameters)

  def isEmpty : Boolean = SFAUtilities.isEmpty()

  def apply(word : Seq[ITerm]) : Boolean = underlying.accepts(word.toList.asJava, pt)

  lazy val initialState : Int = underlying.getInitialState

  lazy val states : Iterable[Integer] = underlying.getStates.asScala

  lazy val acceptingStates : Iterable[Integer] = underlying.getFinalStates.asScala

  lazy val transitions : Iterable[SFAMove[Conjunction, ITerm]] = underlying.getTransitions.asScala
}

// TODO list of sort of the parameters
class ParametricAutomatonBuilder(val sort : Sort) {

  val pt: ParameterTheory = ParameterTheory(sort, List(sort))
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

  def getAutomaton : ParametricAutomaton = {
    new ParametricAutomaton(SFA.MkSFA(transitions.asJava, init, acceptingStates.asJava, pt), pt, parameters)
  }

  def makeUniversal : ParametricAutomaton = {
    new automataIntern.ParametricAutomaton(SFA.getFullSFA(pt), pt, 0)
  }

}
