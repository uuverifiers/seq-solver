

package seqSolver

import ap.api.SimpleAPI
import ap.basetypes.IdealInt
import ap.parser.{ITerm, IIntLit}
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.{TerForConvenience, Term, Formula, VariableTerm}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import ap.theories.TheoryRegistry
import ap.types.SortedPredicate
import ap.util.LRUCache
import seqSolver.automataIntern.Automaton
import seqSolver.preop.{ConcatPreOp, PreOp}
import ap.util.Seqs

import scala.collection.mutable.ArrayBuffer

object SeqTheoryPlugin {

  val enableAssertions = true

}

class SeqTheoryPlugin(theory : SeqTheory) extends Plugin {
  import SeqTheoryPlugin._

  import theory.{seq_in_re_id, seq_++, seq_empty, seq_cons, FunPred,
    parameterTerms, _parameterFuns, _charParameterFun,
    seqConstant, _seq_empty, _seq_cons}
  private val modelCache =
    new LRUCache[Conjunction, Option[Map[Term, Seq[ITerm]]]](3)

  val bwdPropHandledPreds =
    theory.predicates filterNot { p => p == _seq_empty || p == _seq_cons }

  override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
    goalState(goal) match {
      case Plugin.GoalState.Final =>
        if (!Seqs.disjointSeq(goal.facts.predicates, bwdPropHandledPreds)) {
          println
          println("have to solve: " + goal.facts)
          callBackwardProp(goal)
        } else {
          List()
        }
      case _ => {
        List()
      }
    }

  private def callBackwardProp(goal : Goal) : Seq[Plugin.Action] =
    modelCache(goal.facts) {
      // TODO: make cache more precise, filter out in particular
      // seqConstant atoms
      findModel(goal)
    } match {
      case Some(m) => {
        // handleSolution(goal, m)
        println("Found solution: " + m)

        // mark the symbols in the solution to make sure that nobody
        // else will replace them by values
        implicit val o = goal.order
        import TerForConvenience._
        val facts = goal.facts.predConj

        val modelConstants =
          (m.keys.flatMap(_.constants).toSet & o.orderedConstants) ++
          (for (p <- _parameterFuns.iterator ++ Iterator(_charParameterFun);
                a <- facts.positiveLitsWithPred(p).iterator;
                c <- a.constants)
           yield c)

        val preds =
          goal.reduceWithFacts(
            conj(for (c <- modelConstants) yield seqConstant(List(l(c)))))

        if (preds.isTrue)
          List()
        else
          List(Plugin.AddAxiom(List(), preds, theory))
      }
      case None => {
        List(Plugin.AddFormula(Conjunction.TRUE))
      }
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
//      println(goal.facts.arithConj)
      pProver.addAssertion(goal.facts.arithConj)

      implicit val o = pProver.order
      import TerForConvenience._

      val equations =
        conj(for ((c, t) <- theory.enumParameterTerms(goal)) yield (c === t))

      pProver.addAssertion(equations)

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

  override def computeModel(goal : Goal) : Seq[Plugin.Action] =
    if (Seqs.disjointSeq(goal.facts.predicates, bwdPropHandledPreds)) {
      List()
    } else {
      println
      println("computeModel: " + goal.facts)

      implicit val order = goal.order
      import TerForConvenience._

      val model = (modelCache(goal.facts) {
                     // TODO: make cache more precise, filter out in particular
                     // seqConstant atoms
                     findModel(goal)
                   }).get

      val seqFormulas =
        conj(goal.facts.iterator filter {
               f => !Seqs.disjointSeq(f.predicates, theory.predicates)
             })

      var varCnt = 0
      val extraFors = new ArrayBuffer[Formula]
      
      def newVar : VariableTerm = {
        varCnt = varCnt + 1
        v(varCnt - 1)
      }

      def translateElement(t : ITerm) : LinearCombination = t match {
        case IIntLit(value) => l(value)
      }

      // Translate the values of sequence variables
      for ((t, seq) <- model)
        if (t.constants subsetOf order.orderedConstants) {
          val startId = newVar
          extraFors += Atom(_seq_empty, List(l(startId)), order)

          val finalId = seq.foldRight(startId) {
            case (el, id) => {
              val nextId = newVar
              extraFors += Atom(_seq_cons,
                                List(translateElement(el),
                                     l(id), l(nextId)), order)
              nextId
            }
          }

          extraFors += (t === finalId)
        }

      // Translate the values of parameters
      for ((c, t) <- theory.enumParameterTerms(goal)) {
        val seq = model(c)
        assert(seq.size == 1)
        extraFors += (t === translateElement(seq.head))
      }

      val solutionFormula = exists(varCnt, conj(extraFors))

      List(Plugin.RemoveFacts(seqFormulas),
           Plugin.AddAxiom(List(seqFormulas), solutionFormula, theory))
    }


/*
  def handleSolution(goal : Goal,
                     model : Map[Term, Seq[ITerm]]) : Seq[Plugin.Action] = {
    val predConj = goal.facts.predConj
    val allAtoms = predConj.positiveLits ++ predConj.negativeLits
    val nonTheoryAtoms =
      allAtoms filterNot {
        a => TheoryRegistry.lookupSymbol(a.pred) match {
          case Some(`theory`) => true
          case _ => false
        }
      }

    val encodedSeqs =
      (for (a <- nonTheoryAtoms.iterator;
            sorts = SortedPredicate argumentSorts a;
            (t@LinearCombination.Constant(IdealInt(id)), theory.SeqSort) <- a.iterator zip sorts.iterator)
        yield (t, theory.autDatabase id2Aut id)).toVector

    val extModel = (model)// ++ encodedSeqs).toMap

    val variableClasses =
      (for ((t, w) <- extModel.iterator)
        yield (t,w)).toList groupBy(_._2)

    println("predconj: " + predConj + " allatoms: " + allAtoms + " nontheory atoms: " + nonTheoryAtoms + " encodedseqs : " + encodedSeqs +"variable classes " + variableClasses)

    // TODO
    if (variableClasses forall { case (_, c) => c.size <= 1 })
      return List()

    val interestingConstants =
      (for (a <- nonTheoryAtoms; c <- a.constants) yield c).toSet

    /*

   println("interesting constants " + interestingConstants)

    if (interestingConstants.isEmpty)
      return List()
    */
    implicit val order = goal.order
    import TerForConvenience._

    println("variable classes " + variableClasses.keySet + " interesting constants " + interestingConstants)
    (for (w <- variableClasses.keySet.toSeq.iterator;
          terms = variableClasses(w) map (_._1);
          interestingTerms = terms filter {
            t => t.constants.isEmpty ||
              !Seqs.disjoint(t.constants, interestingConstants)
          };
          if interestingTerms.size > 1 &&
            interestingTerms.exists(!_.constants.isEmpty)) yield {
      val allEq =
        conj(for (Seq(t1, t2) <- interestingTerms sliding 2) yield t1 === t2)
      Plugin.AxiomSplit(List(),
        (allEq, List()) :: (
          for (eq <- allEq.iterator)
            yield (!eq, List())).toList,
        theory)
    }).toStream.headOption.toSeq
  }
 */
}
