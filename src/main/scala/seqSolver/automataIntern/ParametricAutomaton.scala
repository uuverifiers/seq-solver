package seqSolver.automataIntern

import ap.api.SimpleAPI
import ap.parser.ITerm
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Conjunction
import ap.types.Sort
import automata.sfa.{SFA, SFAEpsilon, SFAInputMove, SFAMove}
import seqSolver.{ParameterTheory, SFAUtilities, SeqTheory, automataIntern}
import seqSolver.automataIntern.ParametricAutomaton.toSFA

import java.util
import scala.collection.mutable
import scala.collection.JavaConverters._
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet, Stack => MStack}



object ParametricAutomaton {
  def toSFA(aut : Automaton) : SFA[Conjunction, ITerm] = aut match {
    case that : ParametricAutomaton => that.underlying
    case _ =>
      throw new IllegalArgumentException
  }



  def makeUniversal(seqTheory : SeqTheory) : ParametricAutomaton = {
    val pt: ParameterTheory = ParameterTheory(seqTheory.sort, List(seqTheory.sort))
    new ParametricAutomaton(SFA.getFullSFA(pt), pt)
  }

  def reverseAut(aut : Automaton) : Automaton = aut match {
    case that : ParametricAutomaton => {

      val builder = new ParametricAutomatonBuilder(that.parameterTheory)
      /*
      To reverse an automaton we introduce on additional state which is going to be the initial state.
      Put in epsilon transitions from new initial state to all final states
      then for all transitions flip it around with the same guard
      final state is the initial state
       */
       builder.setAccepting(aut.initialState)
      // TODO new state?
       builder.setInitialState(aut.stateCount)
      for (transition <- that.getAllSuccessors(that.states.toList)) {
        transition match {
          case input : SFAInputMove[Conjunction, ITerm] => {
            builder.addTransition(transition.to, transition.from, input.guard)
          }
          case _ : SFAEpsilon[Conjunction, ITerm] => {
            builder.addETransition(transition.to, transition.from)
          }
        }

      }
      for (accepting <- that.acceptingStates) {
        builder.addETransition(builder.init, accepting)
      }
      builder.getAutomaton
    }
    case _ =>
      throw new IllegalArgumentException
  }


}

class ParametricAutomaton(val underlying : SFA[Conjunction,ITerm], pt : ParameterTheory) extends Automaton {

  val parameterTheory: ParameterTheory = pt

  override def stateCount : Int = underlying.stateCount()

  override def toString: String = underlying.toString

  override def isAccept(s: Integer) : Boolean = acceptingStates.contains(s)

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
  override def unary_! : Automaton = {
    /*
    Requires automaton to be deterministic and parameters to only be used as assignment

     */
    val builder = new ParametricAutomatonBuilder(pt)
    /*
    initial state stays the same
    then for each state we look at all outgoing transitions
    we need a map that maps from new state to old states

     */

    val oldToNew = new MHashMap[Int, Int]
    val epsilonFree = underlying.removeEpsilonMoves(pt)
  //  println("eps free" + epsilonFree)
    val init = builder.getNewState
    builder.setInitialState(init)
    oldToNew.put(epsilonFree.getInitialState,init)

    val visited = new MHashSet[Int]
    val toVisit = new MStack[Int]
    toVisit.push(epsilonFree.getInitialState)
    val usedParameters = new MHashSet[ConstantTerm]


    while (toVisit.nonEmpty){
      val current_state = toVisit.pop()

      visited.add(current_state)
    //  println("visiting state " + current_state)

      val new_state1 = oldToNew.getOrElseUpdate(current_state, builder.getNewState)
      if (!epsilonFree.isFinalState(current_state)){
        builder.setAccepting(new_state1)
      //  println("setting state: " + new_state1 + " to accepting state")
      }
      val incompleteConj = new MHashSet[Conjunction]
      for (transition <- getSuccessors(current_state)) {
        val new_state2 = oldToNew.getOrElseUpdate(transition.to, builder.getNewState)

        /*
        check for the following to cases:
        1. we have a first assign for a parameter here
          1.1 keep the transition and do not include it, save that this parameter has been used
        2. we have no parameters as outgoing transitions
          2.1 compute the complete transition that is missing and add it to a newly created final state
        3. we have transitions that have no parameters and we have a first assign
          compute the complete transition excluding the parameter transition but save that this parameter has been used TODO branching is allowed
        4. we have a second assign for a parameter here
          include the parameter guard in the complete transition
        5. no successors means we need one sigma transition

         */

        builder.addTransition(new_state1, new_state2, transition.guard)
       // println("add new transition from: " + new_state1 + " to: " + new_state2, " with guard: " + transition.guard)
        var containsParameters = false
        for (p <- pt.parameters){
          if (transition.guard.constants.contains(p)){
            if (usedParameters.contains(p)){
              // guard was already used as assignment
              incompleteConj.add(pt.MkNot(transition.guard))
              containsParameters = true
            }
            else{
              // guard is just an assignment and does not need to be negated
              usedParameters.add(p)
              containsParameters = true
            }
          }
        }
        // the guard contains no parameters
        if (!containsParameters){
          incompleteConj.add(pt.MkNot(transition.guard))
        }
        if (!visited.contains(transition.to)){
          toVisit.push(transition.to)
        }
      }
      // all successors have been looked at and the conjunction that makes the postimage complete has been computed
      val newCompleteState = builder.getNewState
      if (incompleteConj.isEmpty){
      //  println("incompletecon is empty")

        builder.addTransition(new_state1, newCompleteState, Conjunction.FALSE)
      }
      else{
        builder.addTransition(new_state1, newCompleteState, pt.MkAnd(incompleteConj.asJava))
        builder.addTransition(newCompleteState, newCompleteState, Conjunction.TRUE)
      }
    //  println("add new transition from: " + new_state1 + " to: " + newCompleteState, " with guard: " + pt.MkAnd(incompleteConj.asJava))
      builder.setAccepting(newCompleteState)
    //  println("setting state: " + newCompleteState + " to accepting state")
    }
    builder.getAutomaton
  }

  def getSuccessors(s: Integer): Iterable[SFAInputMove[Conjunction, ITerm]] = {
    underlying.getInputMovesFrom(s).asScala
  }

  def getAllSuccessors(s: Integer) : Iterable[SFAMove[Conjunction, ITerm]] = {
    underlying.getTransitionsFrom(s).asScala
  }
  def getAllSuccessors(s: List[Integer]) : Iterable[SFAMove[Conjunction, ITerm]] = {
    underlying.getTransitionsFrom(s.asJava).asScala
  }

  def isEmpty : Boolean = {
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
  def addETransition(from : Int, to : Int) : Unit = {
    val l = new SFAEpsilon[Conjunction, ITerm](from, to)
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
