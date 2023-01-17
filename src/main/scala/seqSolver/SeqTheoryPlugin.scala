

package seqSolver

import ap.api.SimpleAPI
import ap.parser.ITerm
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.{TerForConvenience, Term}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import ap.util.LRUCache
import seqSolver.automataIntern.Automaton
import seqSolver.preop.{ConcatPreOp, PreOp}

import scala.collection.mutable.ArrayBuffer

object SeqTheoryPlugin {

  val enableAssertions = true

}

class SeqTheoryPlugin(theory : SeqTheory) extends Plugin {
  import SeqTheoryPlugin._

  import theory.{seq_in_re_id, seq_++, seq_empty, seq_cons, seq_head, seq_tail, FunPred, parameterTerms}
  private val modelCache = new LRUCache[Conjunction, Option[Map[Term, Seq[ITerm]]]](3)


  override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
    goalState(goal) match {
      case Plugin.GoalState.Final => {
        println("have to solve: " + goal.facts)
        callBackwardProp(goal)
      }
      case _ => {
        List()
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
    println("preds" + theory.predicates + "parameter terms " + parameterTerms)
    for (a <- atoms.positiveLits) a.pred match {
      case `seq_in_re_id` => decodeRegexID(a, false)
      case p if (theory.predicates contains p  ) =>
        translateFunction(a) match {
          case Some((op, args, res)) =>
            funApps += ((op(), args, res))
          case _ => println("ignoring " + p + " for backwards prop")//throw new Exception("Cannot handle literal " +a)
        }

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

    SimpleAPI.withProver(enableAssert = enableAssertions) { pProver =>
//      pProver setConstructProofs true
      pProver addConstantsRaw(order sort order.orderedConstants)

      pProver addTheories theory.parameterTheory.theories
      pProver addConstantsRaw theory.parameterTheory.parameters

      pProver.addAssertion(goal.facts.arithConj)

      implicit val o = pProver.order
      import TerForConvenience._

      val equations =
        for ((p, t) <- theory.parameterPreds zip theory.parameterTheory.parameters;
             a <- goal.facts.predConj.positiveLitsWithPred(p))
        yield (a.head - t)

      pProver.addAssertion(equations === 0)

      val exploration = Exploration.lazyExp(funApps,theory, pProver, regexes)
      val res = exploration.findModel

      println("Result of exploration: " + res)

      res
    }
  }
  def translateFunction(a : Atom) : Option[(() => PreOp, Seq[Term], Term)] = a.pred match {
    case FunPred(`seq_++`) =>
      Some((() => ConcatPreOp, List(a(0),a(1)),a(2)))
    case _ => None//throw new Exception("Function not handled: " + a)
  }
}
