

package seqSolver.automataIntern

import seqSolver._

import scala.collection.mutable.{HashMap => MHashMap}


class AutDatabase(theory : SeqTheory) {

  val parameterTheory = theory.parameterTheory

  private var nextId    = 0
  private val id2AutMap = new MHashMap[Int, Automaton]

  def id2Aut(id : Int) : Automaton = synchronized {
    id2AutMap(id)
  }

  def registerAut(aut : Automaton) : Int = synchronized {
    val id = nextId
    nextId = nextId + 1
    id2AutMap.put(id, aut)
    id
  }

}
