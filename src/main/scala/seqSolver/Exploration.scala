package seqSolver

import ap.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
import ap.parser.IExpression.Sort
import ap.parser.{IExpression, ITerm}
import ap.terfor.{ConstantTerm, Term}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.substitutions.{ConstantSubst, VariableSubst}
import ap.util.Seqs
import automata.sfa.{SFA, SFAEpsilon, SFAInputMove}
import seqSolver.Exploration.{ConflictSet, ConstraintStore, FoundModel, TermConstraint}
import seqSolver.automataIntern.{Automaton, ParametricAutomaton}
import seqSolver.preop.PreOp

import scala.util.Left
import scala.collection.immutable.Nil.distinct
import scala.collection.{breakOut, mutable}
import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}

object Exploration {

  case class TermConstraint(t : Term, aut : Automaton)

  type ConflictSet = Seq[TermConstraint]

  abstract class ConstraintStore {
    def push : Unit

    def pop : Unit

    /**
     * Add new automata to the store, return a sequence of term constraints
     * in case the asserted constraints have become inconsistent
     */
    def assertConstraint(aut : Automaton) : Option[ConflictSet]

    /**
     * Return some representation of the asserted constraints
     */
    def getContents : List[Automaton]

    /**
     * Return all constraints that were asserted (without any modifications)
     */
    def getCompleteContents : List[Automaton]

    /**
     * Make sure that the exact length abstraction for the intersection of the
     * stored automata has been pushed to the length prover
     */
    def ensureCompleteLengthConstraints : Unit

    /**
     * Check whether some word is accepted by all the stored constraints
     */
    def isAcceptedWord(w : Seq[ITerm]) : Boolean

    /**
     * Produce an arbitrary word accepted by all the stored constraints
     */
    def getAcceptedWord : Seq[ITerm]

    /*/**
     * Produce a word of length <code>len</code> accepted by all the stored
     * constraints
     */
    def getAcceptedWordLen(len : Int) : Seq[Int]*/
  }


  def lazyExp(funApps: Seq[(PreOp, Seq[Term], Term)],
              seqTheory : SeqTheory,
              parameterProver : SimpleAPI,
              initialConstraints : Seq[(Term,Automaton)]
             ) : Exploration = new LazyExploration(funApps,seqTheory, parameterProver, initialConstraints)

  private case class FoundModel(model : Map[Term, Seq[ITerm]])
    extends Exception

}

abstract class Exploration(val funApps: Seq[(PreOp, Seq[Term], Term)],
                           seqTheory : SeqTheory,
                           parameterProver : SimpleAPI,
                           val initialConstraints : Seq[(Term, Automaton)]) {


  //println("Running backwards propagation")

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

  val nonTreeLikeApps =
    sortedFunApps exists {
      case (ops, t) => ops.size > 1
    }

  if (nonTreeLikeApps)
    Console.err.println(
      "Warning: input is not straightline, some variables have multiple " +
      "definitions")

  val resultTerms: Set[Term] =
    (for ((_, t) <- sortedFunApps.iterator) yield t).toSet
  val leafTerms =
    allTerms filter {
      case t => !(resultTerms contains t)
    }


  val allInitialConstraints = {
    val term2Index =
      (for (((_, t), n) <- sortedFunApps.iterator.zipWithIndex)
        yield (t -> n )).toMap

    val coveredTerms = new MBitSet
    for ((t, _) <- initialConstraints)
      for (ind <- term2Index get t)
        coveredTerms += ind

    val additionalConstraints = new ArrayBuffer[(Term, Automaton)]

    for (n <- 0 until sortedFunApps.size;
      if {
        if (!(coveredTerms contains n)) {
          coveredTerms += n
          additionalConstraints += ((sortedFunApps(n)._2, ParametricAutomaton.makeUniversal(seqTheory)))

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

  def findModel : Option[Map[Term, Seq[ITerm]]] = {
    for (t <- allTerms)
      constraintStores.put(t, newStore(t))

    for ((t, aut) <- allInitialConstraints) {
      constraintStores(t).assertConstraint(aut) match {
        case Some(_) => return None
        case None => //nothing
      }
    }

    val funAppList =
      (for ((apps, res) <- sortedFunApps;
            (op, args) <- apps)
      yield (op, args, res)).toList
    try {
      dfExplore(funAppList)
      None
    } catch {
      case FoundModel(model) => Some(model)
    }
  }

  // TODO: simpleapi.partialmodel not defined? may not be needed
  private def evalTerm(t : Term)(model : SimpleAPI) : Option[ITerm] = t match {
    case c : ConstantTerm => Some(model.evalToTerm(c))
    case _ => None
  }


  private def dfExplore(apps : List[(PreOp, Seq[Term], Term)]) : ConflictSet = apps match {


    case List() => {
      import ap.parser.IExpression._
      val model = new MHashMap[Term, Seq[ITerm]]

      val input = new ArrayBuffer[Automaton]
      for (t <- leafTerms){
        val store = constraintStores(t)
        // TODO store contents can be empty?
        val _tmpIntersection = SFAUtilities.intersection(store.getContents)
        if (_tmpIntersection.nonEmpty){
          input += _tmpIntersection.get
        }
      }
      // TODO vereinfache disjunktion zu konjunktion
      val _tmp2 = new MHashMap[Automaton, MHashMap[Integer, MHashSet[Seq[Conjunction]]]]()

      val prover = SimpleAPI(enableAssert = SeqTheoryPlugin.enableAssertions)
      prover addTheories seqTheory.parameterTheory.theories
      prover addConstantsRaw seqTheory.parameterTheory.parameters
      prover addConstantsRaw seqTheory.parameterTheory.charSymbols

      val result = parameterCheck(input.toList, prover, _tmp2)


      // TODO put parameters in model
      if (result.isEmpty){
        // extract model
        for ((t, word) <- leafTerms zip words) {
          model.put(t, (for (l <- word) yield evalTerm(l)(parameterProver).get).toList)

        }
        for (p <- seqTheory.parameterTheory.parameters){
          prover.addAssertion(p === evalTerm(p)(parameterProver).get)
          model.put(p, Seq(evalTerm(p)(parameterProver).get))
        }
        val allFunApps : Iterator[(PreOp, Seq[Term], Term)] =
          (for ((ops, res) <- sortedFunApps.reverseIterator;
                (op, args) <- ops.iterator)
          yield (op, args, res)) ++ ignoredApps.iterator




        for ((op, args, res) <- allFunApps;
             argValues = args map model) {

          //
          val resSeq = op.eval(argValues, prover) match {
            case Some(v) => v
            case None => {
              throw new Exception(
                "model extraction failed: " + op + "is not defined for " + argValues)
            }
          }

          Console.err.println("Derived model value: " + res + " <- " + resSeq)
          val resValue = resSeq
          for (oldValue <- model get res) {

            // TODO: nonTreeLikeApps?
            if (resValue != oldValue){
              // TODO: throw backward failed exception?
              throw new Exception("Model Extraction failed")
            }
          }
          // TODO is accepted implementation
          if (!(constraintStores(res).isAcceptedWord(resSeq)))
            throw new Exception(
              "Could not satisfy regex constraints for " + res +
                ", maybe the problems involves non-functional transducers?")

          model.put(res, resValue)
        }
        throw FoundModel(model.toMap)
      }
      else{
        result.get
      }
    }

    case (op, args, res) :: otherApps => {
      //Console.err.println("dfExplore, depth " + apps.size)
      dfExploreOp(op, args, res, constraintStores(res).getContents,
        otherApps)
    }
  }

  private def dfExploreOp(op: PreOp, args: Seq[Term], res: Term, resConstraints: List[Automaton], nextApps: List[(PreOp, Seq[Term], Term)]) : ConflictSet = resConstraints match {
    case List() => dfExplore(nextApps)

    case resAut :: otherAuts => {
      ap.util.Timeout.check

      val collectedConflicts = new LinkedHashSet[TermConstraint]

      val newConstraintsIt = op(resAut, seqTheory)

      while (newConstraintsIt.hasNext){
        val argCS = newConstraintsIt.next()
        for (a <- args)
          constraintStores(a).push
        try {
          val newConstraints = new MHashSet[TermConstraint]

          var consistent = true
          for ((a, aut) <- args zip argCS)
            if (consistent) {
              newConstraints += TermConstraint(a, aut)
              constraintStores(a).assertConstraint(aut) match {
                case Some(conflict) => {
                  consistent = false
                  Seqs.disjointSeq(newConstraints, conflict)
                  collectedConflicts ++= (conflict.iterator.filterNot(newConstraints))
                }
                case None => // nothing
              }
            }

          if (consistent) {
            val conflict = dfExploreOp(op, args, res, otherAuts, nextApps)
            if(Seqs.disjointSeq(newConstraints, conflict)) {
              // we can jump back because the found conflict does not depend on the considered fun app
              return conflict
            }
            collectedConflicts ++= (conflict.iterator filterNot newConstraints)
          }
        } finally {
          for (a <- args) {
            constraintStores(a).pop
          }

        }
      }
      collectedConflicts.toSeq
    }
  }


  private val parameterPartitionStack = new ArrayStack[Int]
  private val parameterPartitions = new ArrayBuffer[Seq[TermConstraint]]

  protected def addParameterConstraint(constraint : TermConstraint, sources : Seq[TermConstraint]) : Unit = {
    parameterPartitions += sources
    parameterProver setPartitionNumber(parameterPartitions.size)
    val TermConstraint(t, aut) = constraint
    // TODO add generate formula from the constraint
  }

  private def checkParameterConsistency(): Option[Seq[TermConstraint]] = {
    if (parameterProver.??? == ProverStatus.Unsat) {
      Some(for (n <- parameterProver.getUnsatCore.toList.sorted; if n > 0; c <- parameterPartitions(n-1)) yield c)
    }
    else
      None
  }

  private def pushParameterConstraint() : Unit = {
    parameterProver.push
    parameterPartitionStack.push(parameterPartitions.size)

  }


  private def popLengthConstraints() : Unit = {
    parameterProver.pop
    parameterPartitions reduceToSize(parameterPartitionStack.size)
  }

  protected def newStore(t : Term) : ConstraintStore

  protected val needCompleteContentsForConflicts : Boolean

  val words : ArrayBuffer[ArrayBuffer[ConstantTerm]]

  // TODO sequences of conjunctions
  // TODO kann man vorberechnen für jeden automaton
  def parameterCheck(allAutomata : List[Automaton], prover : SimpleAPI, automaton_to_constraints : MHashMap[Automaton,MHashMap[Integer, MHashSet[Seq[Conjunction]]]]): Option[Seq[TermConstraint]] = prover.scope{

    allAutomata match {
      case aut1 :: otherauts => {

        val aut = aut1.asInstanceOf[ParametricAutomaton]
        val constraints = automaton_to_constraints.getOrElse(aut, new MHashMap)
        val path_set = new MHashSet[Integer]
        val s = mutable.Stack[Int]()
        val _tmpset = new MHashSet[Seq[Conjunction]]()
        _tmpset.add(Seq(Conjunction.TRUE))
        constraints.put(aut.initialState, _tmpset)
        s.push(aut.initialState)
        while (s.nonEmpty){
          val current_state = s.pop()
          if (aut.acceptingStates.contains(current_state)){
            // get the set of constraints associated to the state
            constraints.get(current_state) match {
              case None => {
                throw new Exception("Final state with no constraints? Return True?")
              }
              case Some(constraint_bags) => {

                for (conjunction <- constraint_bags){

                  parameterProver.push
                  var counter = 0
                  val tmp_conjunction = new ArrayBuffer[Conjunction]
                  val tmp_word = new ArrayBuffer[ConstantTerm]

                  for (conj <- conjunction){
                    // pfad speichern
                    if (conj != Conjunction.TRUE){
                      val new_const = seqTheory.parameterTheory.charSort newConstant("l" + counter)
                      counter += 1
                      parameterProver.addConstant(new_const)
                      val z = ConstantSubst(seqTheory.parameterTheory.charSymbol, new_const, parameterProver.order)(conj)

                      tmp_conjunction += z
                      tmp_word += new_const
                    }
                  }

                  parameterProver.addAssertion(Conjunction.conj(tmp_conjunction, parameterProver.order))
                  // if it is sat then we have found a viable path and can continue onwards
                  path_set.add(current_state)
                  if (parameterProver.??? == ProverStatus.Sat){
                    words += tmp_word
                    // the next check might come to the conclusion that this path cannot be part of the solution
                    // TODO none = sat; otherwise return conflicts
                    val l = parameterCheck(otherauts, prover, automaton_to_constraints)
                    if (l.isEmpty) {
                      return None
                    }
                    else{
                      // TODO conflicts??
                      words.remove(words.size-1)
                    }
                  }
                  else{

                    // Nothing, keep searching, i.e. go to the next state in the stack
                  }
                  parameterProver.pop
                }
              }
            }
          }
          else{
            // for all successors do
            val all_transitions = aut.getAllSuccessors(current_state)
            // TODO Handle epsilon?
            for (successor <- all_transitions){
              val _tmpset = constraints(current_state)
              val successor_conj = constraints.getOrElse(successor.to, new MHashSet[Seq[Conjunction]]())
              // TODO bug with successor conj where tmp set is not removed
              // get the current possible conjs
              constraints.get(current_state) match {
                case None => {
                  throw new Exception("Final state with no constraints? Return True?")
                }
                case Some(constraint_bags) => {
                  var successor_new_bag = new MHashSet[Seq[Conjunction]]()
                  for (conjunction <- constraint_bags){
                    var new_conj = conjunction
                    // change for sequence
                    successor match {
                      case epsilon: SFAEpsilon[_, _] => new_conj ++= Seq(Conjunction.TRUE)
                      case move: SFAInputMove[_, _] => new_conj ++= Seq(move.guard)
                      case _ =>
                    }

                    var subset = false
                    for (successor_con <- successor_conj){
                      if (new_conj.toSet.subsetOf(successor_con.toSet)){
                        subset = true
                        // TODO break?
                      }
                    }

                    if (subset) {
                      successor_new_bag = constraint_bags
                      // do nothing
                    }
                    else{
                      // TODO checking this is not that straightforward
                      var counter = 0
                      val tmp_conjunction = new ArrayBuffer[Conjunction]
                      // TODO keep a set of constants and only create new ones when we run out?
                      for (conj <- new_conj){
                        val new_const = seqTheory.parameterTheory.charSort newConstant("a" + counter)
                        counter += 1
                        prover.addConstant(new_const)
                        val z = ConstantSubst(seqTheory.parameterTheory.charSymbol, new_const, prover.order)(conj)
                        tmp_conjunction += (z)
                      }
                      prover.scope{
                        prover.addAssertion(Conjunction.conj(tmp_conjunction, prover.order))
                        // TODO maybe faster without this check?
                        if (prover.??? == ProverStatus.Sat){
                          s.push(successor.to)
                          successor_new_bag += (new_conj)
                          //constraints.put(successor.to, successor_conj)
                        }
                        else{
                          // collect conflicts?
                        }
                      }
                    }
                  }
                  constraints.put(successor.to, successor_new_bag)
                }
              }
            }
          }
        }
        // after stack is empty, the entire bag constraints have been computed
        for (final_state <- aut.acceptingStates){
          if (path_set.contains(final_state)){
            // do nothing because this has already been checked
          }
          else{
            constraints.get(final_state) match {
              case None => {
                return Some(List())
              }
              case Some(constraint_bags) => {
                for (conjunction <- constraint_bags){
                  parameterProver.push
                  // TODO check if it is sat for entire automaton up to here
                  var counter = 0
                  val tmp_conjunction = new ArrayBuffer[Conjunction]
                  val tmp_word = new ArrayBuffer[ConstantTerm]
                  // TODO keep a set of constants and only create new ones when we run out?
                  for (conj <- conjunction){
                    val new_const = seqTheory.parameterTheory.charSort newConstant("a" + counter)
                    counter += 1
                    parameterProver.addConstant(new_const)
                    val z = ConstantSubst(seqTheory.parameterTheory.charSymbol, new_const, parameterProver.order)(conj)
                    tmp_conjunction += (z)
                    tmp_word += new_const
                  }
                  parameterProver.addAssertion(Conjunction.conj(tmp_conjunction, prover.order))
                  // if it is sat then we have found a viable path and can continue onwards
                  path_set.add(final_state)
                  if (parameterProver.??? == ProverStatus.Sat){
                    words += tmp_word
                    val l = parameterCheck(otherauts, prover, automaton_to_constraints)
                    if (l.isEmpty) {
                      return None
                    }
                    else{
                      words.remove(words.size-1)
                    }
                  }
                  else{
                    // Nothing, keep searching, i.e. go to the next state in the stack
                  }
                  parameterProver.pop
                }
              }
            }
          }
        }
        return Some(List())
      }
      case List() => {
        return None
      }
    }
  }

}

/**
 * Lazy exploration without explicit computation of products
 */


class LazyExploration(_funApps : Seq[(PreOp, Seq[Term], Term)],
                      _seqTheory : SeqTheory,
                      _parameterProver : SimpleAPI,
                      _initialConstraints : Seq[(Term, Automaton)])
      extends Exploration(_funApps, _seqTheory, _parameterProver, _initialConstraints) {
  import Exploration._





  override protected val needCompleteContentsForConflicts: Boolean = false

  private val stores = new ArrayBuffer[Store]

  // combinations of automata known to have empty intersection
  private val inconsistentAutomata = new ArrayBuffer[Seq[Automaton]]

  private def addIncAutomata(auts : Seq[Automaton]) : Unit = {
    inconsistentAutomata += auts
    val ind = inconsistentAutomata.size - 1
    for (s <- stores) {
      val r = s.watchAutomata(auts, ind)
      assert(r)
    }
  }

  protected def newStore(t: Term): ConstraintStore = new Store(t)

  private class Store(t : Term) extends ConstraintStore {

    private val constraints = new ArrayBuffer[Automaton]
    private val constraintSet = new MHashSet[Automaton]
    private val constraintStack = new mutable.ArrayStack[Int]

    // Map from watched automata to the indexes of
    // <code>inconsistentAutomata</code> that is watched
    private val watchedAutomata = new MHashMap[Automaton, List[Int]]

    def watchAutomata(auts : Seq[Automaton], ind : Int) : Boolean =
      (auts find {a => !(constraintSet contains a) }match {
        case Some(aut) => {
          watchedAutomata.put(aut, ind :: watchedAutomata.getOrElse(aut, List()))
          true
        }
        case None =>
          false
      })

    override def push: Unit = constraintStack push constraints.size

    override def pop: Unit = {
      val oldSize = constraintStack.pop
      while (constraints.size > oldSize) {
        constraintSet -= constraints.last
        constraints reduceToSize(constraints.size -1)
      }
    }

    /**
     * Add new automata to the store, return a sequence of term constraints
     * in case the asserted constraints have become inconsistent
     */
    override def assertConstraint(aut: Automaton): Option[ConflictSet] =
      if (constraintSet contains aut) {
        None
      } else {
        var potentialConflicts =
          (watchedAutomata get aut) match {
            case Some(incAuts) => {
              watchedAutomata -= aut
              incAuts
            }
            case None =>
              List()
          }

        while(potentialConflicts.nonEmpty) {
          val autInd = potentialConflicts.head

          if (!watchAutomata(inconsistentAutomata(autInd), autInd)){
            //constraints have become inconsistent
            watchedAutomata.put(aut, potentialConflicts)
            return Some(for(a <- inconsistentAutomata(autInd).toList)
                        yield TermConstraint(t,a))
          }

          potentialConflicts = potentialConflicts.tail
        }
        SFAUtilities.findUnsatCore(constraints, aut) match {
          case Some(core) => {
            addIncAutomata(core)
            Some(for (a <- core.toList) yield TermConstraint(t,a))
          }
          case None => {
            constraints += aut
            constraintSet += aut
            None
          }
        }
      }

    /**
     * Return some representation of the asserted constraints
     */
    override def getContents: List[Automaton] = constraints.toList

    /**
     * Return all constraints that were asserted (without any modifications)
     */
    override def getCompleteContents: List[Automaton] = constraints.toList

    private def intersection : Option[Automaton] = SFAUtilities.intersection(constraints)

    /**
     * Make sure that the exact length abstraction for the intersection of the
     * stored automata has been pushed to the length prover
     *
     * Change to consistency solver for parameter?
     */
    override def ensureCompleteLengthConstraints: Unit = ()

    /**
     * Check whether some word is accepted by all the stored constraints
     */

    override def isAcceptedWord(w: Seq[ITerm]): Boolean = {
      constraints forall (_(w, _parameterProver))
    }

    /**
     * Produce an arbitrary word accepted by all the stored constraints
     */

    override def getAcceptedWord: Seq[ITerm] = ???
  }

  override val words: ArrayBuffer[ArrayBuffer[ConstantTerm]] = new ArrayBuffer[ArrayBuffer[ConstantTerm]]()
}
