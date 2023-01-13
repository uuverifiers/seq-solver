

package seqSolver

import ap.api.SimpleAPI
import ap.parser.ITerm
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.Term
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import ap.util.LRUCache
import seqSolver.automataIntern.Automaton
import seqSolver.preop.PreOp

import scala.collection.mutable.ArrayBuffer

class SeqTheoryPlugin(theory : SeqTheory) extends Plugin {
  import theory.{seq_in_re_id, seq_++, seq_empty, seq_cons, seq_head, seq_tail}
  private val modelCache = new LRUCache[Conjunction, Option[Map[Term, Seq[ITerm]]]](3)


  override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
    goalState(goal) match {
      case Plugin.GoalState.Final => {
        println("have to solve: " + goal.facts)
        callBackwardProp(goal)
      }
      case _ => {
        List()
      }
    }
  }
  private def callBackwardProp(goal : Goal) : Seq[Plugin.Action] =

    modelCache(goal.facts) {
      findModel(goal)
    } match {
      case Some(m) => List()//handleSolution(goal, m)
      case None => List(Plugin.AddFormula(Conjunction.TRUE))
    }

  def findModel(goal: Goal) : Option[Map[Term, Seq[ITerm]]] = {
    val atoms = goal.facts.predConj
    val order = goal.order

    val funApps    = new ArrayBuffer[(PreOp, Seq[Term], Term)]
    val regexes    = new ArrayBuffer[(Term, Automaton)]
    val negEqs     = new ArrayBuffer[(Term, Term)]

    def decodeRegexID(a : Atom, complemented : Boolean) : Unit = a(1) match {
      case LinearCombination.Constant(id) => {
        val aut =
          if (complemented)
            theory.autDatabase.id2Aut(id.intValueSafe)
          else
            theory.autDatabase.id2Aut(id.intValueSafe)

        regexes += ((a.head, aut))

      }
      case lc =>
        throw new Exception("Could not decode regex id " + lc)
    }
    for (a <- atoms.positiveLits) a.pred match {
      case `seq_in_re_id` => decodeRegexID(a, false)
      case _ =>
    }

    for (a <- atoms.negativeLits) a.pred match {
      case `seq_in_re_id` => throw new Exception("Complement of Automaton not handled")
      case _ =>
    }

    if (!goal.facts.arithConj.negativeEqs.isEmpty) {
      throw new Exception("cannot handle negative seq equation")
    }

    val interestingTerms =
      ((for ((t, _) <- regexes.iterator) yield t) ++
        (for ((_, args, res) <- funApps.iterator;
              t <- args.iterator ++ Iterator(res)) yield t)).toSet

    SimpleAPI.withProver { parameterProver =>
      val pProver = {

        parameterProver setConstructProofs true
        parameterProver addConstantsRaw(order sort order.orderedConstants)
        // TODO global parameter conjs?
        //parameterProver addAssertion goal.facts.predConj

        parameterProver addTheories theory.parameterTheory.theories
        parameterProver addConstantsRaw theory.parameterTheory.parameters
        implicit val o = parameterProver.order
        (parameterProver)
      }

      val exploration = Exploration.lazyExp(funApps,theory, pProver, regexes)
      val result = exploration.findModel

      result
    }
  }
}
