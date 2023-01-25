

package seqSolver.automataIntern

import seqSolver._

import ap.parser._
import ap.terfor.ConstantTerm

import automata.sfa.SFA
import automata.sfa.SFAInputMove
import automata.sfa.SFAMove

import scala.collection.mutable.{HashMap => MHashMap}
import scala.collection.JavaConverters._


object AutDatabase {

  abstract sealed class ParametricRegex

  /**
   * Regex accepting exactly sequence <code>[c]</code>.
   */
  case class CharRegex(c : ITerm) extends ParametricRegex

  /**
   * Regex accepting exactly sequence <code>[a]</code>, where
   * <code>a</code> is the value of parameter <code>p</code>.
   */
  case class ParamMatchRegex(p : ConstantTerm) extends ParametricRegex

}

class AutDatabase(theory : SeqTheory) {

  import theory.parameterTheory
  import AutDatabase._

  private var nextId      = 0
  private val id2AutMap   = new MHashMap[Int, Automaton]
  private val id2RegexMap = new MHashMap[Int, ParametricRegex]
  private val regex2IdMap = new MHashMap[ParametricRegex, Int]

  def id2Aut(id : Int) : Automaton = synchronized {
    id2AutMap.getOrElseUpdate(id, regex2Aut(id2RegexMap(id)))
  }

  def registerAut(aut : Automaton) : Int = synchronized {
    val id = nextId
    nextId = nextId + 1
    id2AutMap.put(id, aut)
    id
  }

  def registerRegex(r : ParametricRegex) : Int = synchronized {
    regex2IdMap.getOrElseUpdate(r, {
      val id = nextId
      nextId = nextId + 1
      id2RegexMap.put(id, r)
      id
    })
  }

  private def regex2Aut(r : ParametricRegex) : Automaton = r match {

    case CharRegex(_) | ParamMatchRegex(_) => {
      import IExpression._

      val pt     = theory.parameterTheory
      val letter = pt.charSymbol
      val guard  = r match {
        case CharRegex(c) =>
          pt.FromFormula(letter === c)
        case ParamMatchRegex(p) => {
          assert(pt.parameters contains p)
          pt.FromFormula(letter === p)
        }
      }

      val transitions : Seq[pt.SFAMove] = List(
        new SFAInputMove(0, 1, guard)
      )

      val aut = SFA.MkSFA(transitions.asJava, 0,
                          List(new Integer(1)).asJava,
                          pt)
      new ParametricAutomaton(aut, pt)
    }

  }

}
