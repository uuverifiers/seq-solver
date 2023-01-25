package seqSolver.preop

import ap.parser.ITerm
import seqSolver.SeqTheory
import seqSolver.automataIntern.{Automaton, ParametricAutomaton, ParametricAutomatonBuilder, ParametricTransducerBuilder, Transducer}

import scala.collection.mutable.{HashMap => MHashMap, Stack => MStack}
object ReplacePreOp {

  def apply(w : Seq[ITerm], seqTheory: SeqTheory) : PreOp = ReplacePreOpWord(w, seqTheory)

 /* def apply(aut : ParametricAutomaton, seqTheory: SeqTheory) : PreOp =
    ReplacePreOpRegEx(aut, seqTheory)*/
}

object ReplacePreOpWord {
  def apply(w: Seq[ITerm], seqTheory: SeqTheory): ReplacePreOpTran = {
    val wtran = buildWordTransducer(w, seqTheory)
    new ReplacePreOpTran(wtran)
  }
  private def buildWordTransducer(w : Seq[ITerm], seqTheory: SeqTheory) : Transducer = {
    val builder = new ParametricTransducerBuilder(seqTheory.parameterTheory)

    val initState = builder.initialState
    val states = initState::(List.fill(w.size -1)(builder.getNewState))
    val finstates = List.fill(w.size)(builder.getNewState)
    val copyRest = builder.getNewState

    val end = w.size -1
    builder.setAccept(initState, true)
    finstates.foreach(builder.setAccept(_, true))
    builder.setAccept(copyRest, true)
    // recognise word
    // deliberately miss last element
    for (i <- 0 until w.size -1) {
     // builder.addTransition
    }
???
  }
}


/*
object ReplacePreOpRegEx {
  def apply(aut : Automaton, seqTheory: SeqTheory) : PreOp = {
    val tran = buildTransducer(aut, seqTheory)
    new ReplacePreOpTran(tran)
  }

  private def buildTransducer(aut: Automaton, seqTheory: SeqTheory) : Transducer = {
    abstract class Mode
    // not matching
    case object NotMatching extends Mode
    // matching, word read so far could reach any state in frontier
    case class Matching(val frontier : Set[Integer]) extends Mode
    // last transition finished a match and reached frontier
    case class EndMatch(val frontier : Set[Integer]) extends Mode
    // copy the rest of the word after first match
    case object CopyRest extends Mode

    // val labels ?
    val builder = new ParametricTransducerBuilder(seqTheory.parameterTheory)

    // states of transducer have current mode and a set of states that
    // should never reach a final state (if they do, a match has been
    // missed)
    val sMap = new MHashMap[Integer, (Mode, Set[Integer])]
    val sMapRev = new MHashMap[(Mode, Set[Integer]), Integer]

    val worklist = new MStack[Integer]

    def mapState(s : Integer, q : (Mode, Set[Integer])) = {
      sMap += (s -> q)
      sMapRev += (q -> s)
    }

    def getState(m : Mode, noreach : Set[Integer]) : Integer = {
      sMapRev.getOrElse((m, noreach), {
        val s = builder.getNewState
        mapState(s, (m, noreach))
        val goodNoreach = !noreach.exists(aut.isAccept(_))
        builder.setAccept(s, m match {
          case NotMatching => goodNoreach
          case EndMatch(_) => goodNoreach
          case Matching(_) => false
          case CopyRest => goodNoreach
        })
        if (goodNoreach)
          worklist.push(s)
        s
      })
    }

    val autInit = aut.initialState
    val tranInit = builder.initialState

    mapState(tranInit, (NotMatching, Set.empty[Integer]))
    builder.setAccept(tranInit, true)
    worklist.push(tranInit)

    while (!worklist.isEmpty) {
      val ts = worklist.pop()
      val (mode, noreach) = sMap(ts)

      mode match {
        case NotMatching => {
        }
      }
    }

???
  }

}
*/
class ReplacePreOpTran(t : Transducer) extends PreOp {
  override def apply(resultConstraint: Automaton, seqTheory: SeqTheory): Iterator[Seq[Automaton]] = ???

  override def eval(arguments: Seq[Seq[ITerm]]): Option[Seq[ITerm]] = ???
}