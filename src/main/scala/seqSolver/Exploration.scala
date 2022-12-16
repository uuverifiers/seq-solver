package seqSolver

import ap.SimpleAPI
import ap.parser.IExpression.Sort
import ap.parser.ITerm
import ap.terfor.{ConstantTerm, Term}
import ap.terfor.conjunctions.Conjunction
import automata.sfa.SFA
import ostrich.Exploration.ConflictSet
import seqSolver.Exploration.ConstraintStore
import seqSolver.automataIntern.ParametricAutomaton
import seqSolver.preop.PreOp

import scala.collection.immutable.Nil.distinct
import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}

object Exploration {

  case class TermConstraint(t : Term, aut : ParametricAutomaton)

  abstract class ConstraintStore {
    def push : Unit

    def pop : Unit

    /**
     * Add new automata to the store, return a sequence of term constraints
     * in case the asserted constraints have become inconsistent
     */
    def assertConstraint(aut : ParametricAutomaton) : Option[ConflictSet]

    /**
     * Return some representation of the asserted constraints
     */
    def getContents : List[ParametricAutomaton]

    /**
     * Return all constraints that were asserted (without any modifications)
     */
    def getCompleteContents : List[ParametricAutomaton]

    /**
     * Make sure that the exact length abstraction for the intersection of the
     * stored automata has been pushed to the length prover
     */
    def ensureCompleteLengthConstraints : Unit

    /**
     * Check whether some word is accepted by all the stored constraints
     */
    def isAcceptedWord(w : Seq[ConstantTerm]) : Boolean

    /**
     * Produce an arbitrary word accepted by all the stored constraints
     */
    def getAcceptedWord : Seq[ConstantTerm]

    /*/**
     * Produce a word of length <code>len</code> accepted by all the stored
     * constraints
     */
    def getAcceptedWordLen(len : Int) : Seq[Int]*/
  }


  type ConflictSet = Seq[TermConstraint]

  def lazyExp(funApps: Seq[(PreOp, Seq[Term], Term)],
              initialConstraints : Seq[(Term,ParametricAutomaton)]
             ) : Exploration = new Exploration(funApps, initialConstraints)

}

class Exploration(val funApps: Seq[(PreOp, Seq[Term], Term)],
                  val initialConstraints : Seq[(Term, ParametricAutomaton)]) {
  println("Running backwards propagation")

  private val (allTerms, sortedFunApps, ignoredApps)
              : (Set[Term],
                Seq[(Seq[(PreOp, Seq[Term])], Term)],
                Seq[(PreOp, Seq[Term], Term)]) = {
    val argTermNum = new MHashMap[Term, Int]
    // The result terms are mapped to 0
    for ((_,_, res) <- funApps)
      argTermNum.put(res, 0)
    // The initial terms are mapped to 0
    for ((t,_) <- initialConstraints)
      argTermNum.put(t, 0)
    // Save the arguments of the funApps with a counter > 0 if they already appeared
    for ((_, args, _) <- funApps; a <- args)
      argTermNum.put(a, argTermNum.getOrElse(a, 0) +1)

    val ignoredApps = new ArrayBuffer[(PreOp, Seq[Term], Term)]
    var remFunApps  = funApps
    val sortedApps  = new ArrayBuffer[(Seq[(PreOp, Seq[Term])], Term)]

    while(remFunApps.nonEmpty) {
      val (selectedApps, otherApps) =
        remFunApps partition({case (_, _, res) => argTermNum(res) == 0})

      if (selectedApps.isEmpty){
        if (ignoredApps.isEmpty)
          Console.err.println(
            "Warning: cyclic definitions found, ignoring some function " +
              "applications")
        ignoredApps += remFunApps.head
        remFunApps = remFunApps.tail
      } else {

        remFunApps = otherApps

        // reduce selected apps arguments counter by one
        for ((_, args, _) <- selectedApps; a <- args)
          argTermNum.put(a, argTermNum.getOrElse(a, 0) - 1)

        // save the result term of selected apps
        val appsPerRes = selectedApps groupBy(_._3)

        val nonArgTerms = (selectedApps map (_._3)).distinct


        for (t <- nonArgTerms)
          sortedApps +=
            ((for ((op, args, _) <- appsPerRes(t)) yield  (op, args), t))
      }
    }

    (argTermNum.keySet.toSet, sortedApps, ignoredApps)

  }

  val resultTerms: Set[Term] =
    (for ((_, t) <- sortedFunApps.iterator) yield t).toSet
  val leafTerms =
    allTerms filter {
      case t => !(resultTerms contains t)
    }

  // TODO complete the initial constraints
  /*

   */

  val allInitialConstraints = {
    val term2Index =
      (for (((_, t), n) <- sortedFunApps.iterator.zipWithIndex)
        yield (t -> n )).toMap

    val coveredTerms = new MBitSet
    for ((t, _) <- initialConstraints)
      for (ind <- term2Index get t)
        coveredTerms += ind

    val additionalConstraints = new ArrayBuffer[(Term, ParametricAutomaton)]

    // TODO check wheter any of the terms have concrete definition

    for (n <- 0 until sortedFunApps.size;
      if {
        if (!(coveredTerms contains n)) {
          coveredTerms += n
          // TODO get sort from the left side or somewhere else?
          // TODO neuen datentyp
          additionalConstraints += ((sortedFunApps(n)._2, ParametricAutomaton.makeUniversal(Sort.Integer)))

        }
        true
      };
      (_, args) <- sortedFunApps(n)._1;
      arg <- args)
      for (ind <- term2Index get arg)
        coveredTerms += ind

    initialConstraints ++ additionalConstraints

  }


  private val constraintStores = new MHashMap[Term, ConstraintStore]

  // TODO representation for model
  def findModel : Option[Map[Term, ConstantTerm]] = {
    null
  }

  // TODO: simpleapi.partialmodel not defined? may not be needed
  private def evalTerm(t : Term)(model : SimpleAPI) : Option[ConstantTerm] = t match {
    case _ => None
  }

  val funAppList =
    (for ((apps, res) <- sortedFunApps;
          (op, args) <- apps)
      yield (op, args, res)).toList

  /*try {
    dfExplore(funAppList)
    None
  } catch {
    case FoundModel(model) => Some(model)
  }
*/
  // TODO: conflictSet
  private def dfExplore(apps : List[(PreOp, Seq[Term], Term)]) : ConflictSet = apps match {

    case List() => {
      val model = new MHashMap[Term, ConstantTerm]
      // no length model possible

      // TODO compute values for variables
      /*
      for all leaf terms store the constraint
      put inside the model the evaluation of the leafterm
      the evaluation of the leaf term is producing an accepted word from the parametric automaton
       */

      for (t <- leafTerms) {
        val store = constraintStores(t)
        // TODO generate witness must be rewritten
      }
      null
    }

    case _ => null
  }

}
