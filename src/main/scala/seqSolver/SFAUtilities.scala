package seqSolver
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.parser.IExpression.i
import ap.theories.Theory
import ap.parser.{IConstant, IExpression, IFormula, ITerm}
import ap.terfor.TerForConvenience.term2RichLC
import ap.types.Sort
import ap.terfor.{ConstantTerm, Term}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import automata.sfa.{SFA, SFAMove}
import ap.terfor.substitutions.ConstantSubst
import seqSolver.Main.pt
import seqSolver.automataIntern.{Automaton, ParametricAutomaton, ParametricAutomatonBuilder}

import java.util.Collection
import java.util
import scala.collection.mutable
import scala.collection.mutable.Stack
import scala.collection.JavaConverters._
import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}


object SFAUtilities {


  def apply(): SFAUtilities = {
    new SFAUtilities
  }
  def intersection(product : Seq[Automaton]) : Option[Automaton] = product match {

    case aut :: otherAuts => {
      var _tmp = aut
      for (oA <- otherAuts) {
        _tmp = _tmp & oA
      }
      Some(_tmp)
    }
    case List() => {
      None
    }
  }

  def findUnsatCore(oldAuts : Seq[Automaton],
                    newAut : Automaton) : Option[Seq[Automaton]] = {
    val consideredAuts = new ArrayBuffer[Automaton]
    consideredAuts += newAut
    var cont = areConsistentAutomata(consideredAuts)
    val oldAutsIt = oldAuts.iterator
    while (cont && oldAutsIt.hasNext) {
      consideredAuts += oldAutsIt.next()
      cont = areConsistentAutomata(consideredAuts)
    }

    if (cont)
      return None

    // remove automata to get small core
    for (i <- (consideredAuts.size - 2) to 1 by -1) {
      val removedAut = consideredAuts remove i
      if (areConsistentAutomata(consideredAuts))
        consideredAuts.insert(i, removedAut)
    }
    Some(consideredAuts)
  }

  def areConsistentAutomata(automatons: ArrayBuffer[Automaton]) : Boolean =
    if (automatons.isEmpty){
      true
    } else{
      !(automatons.reduceLeft(_ & _)).isEmpty
    }
}

class SFAUtilities {



  def ConstructAllPaths(sfa: SFA[Conjunction, ITerm]): Set[Seq[Integer]] ={
    var res = Set[Seq[Integer]]()
    val s = mutable.Stack[Seq[Integer]]();
    val _tmp = Seq(sfa.getInitialState)
    s.push(_tmp)
    while (s.nonEmpty){
      var current_path = s.pop()
      println(current_path)
      val last = current_path.last
      // Check if last is accepting state, if yes add result and terminate path
      if (sfa.getFinalStates.contains(last)){
        res += current_path
      }
      else{
        val successors_transitions  = sfa.getTransitionsFrom(last).asScala
        val successors = (for (n <- successors_transitions) yield n.to)
        println("l is ", successors)
        for (succ <- successors) {
          //TODO better datastrucutre
          // Save transition
          if (!current_path.contains(succ)){
            // Add all successor paths to the stack
            s.push(current_path ++ Seq(succ))
          }
          else{
            // Terminate this path since a duplicate was found
          }
        }
      }
    }
    res
  }

  // TODO optimization recursive
  def PathFormula(path : Seq[Integer], sfa : SFA[Conjunction, ITerm], pt : ParameterTheory, prover: SimpleAPI): SimpleAPI.ProverStatus.Value = prover.scope {
    // TODO move out
    prover addTheories pt.theories
    prover addConstantsRaw pt.parameters
    prover addConstantsRaw pt.charSymbols

    for (i <- 0 until path.length-1){
      println("Index", i)
      println("Node", path(i))
      println("trans", sfa.getInputMovesFrom(path(i)))
      val _tmp1 = sfa.getInputMovesFrom(path(i))
      for (tmp <- _tmp1.asScala){
        if (tmp.to == path(i+1)){
          //TODO more than one transition can happen?
          println(pt.charSort, pt.order)
          val tmp_assert = (pt.charSort newConstant ("t" + i))
          prover addConstant tmp_assert

          val z = ConstantSubst(pt.charSymbol, tmp_assert, prover.order)(tmp.guard)
          //val z1 = prover.asIFormula(z)
          prover.addAssertion(z)
          println("From", tmp.from, " to ", tmp.to, "guard", z)
        }
        // If there is no input move to this node -> transition has no guard
      }
    }

    (prover.???)
  }

  def EmptinessFormula(sfa : SFA[Conjunction, ITerm], all_paths: Set[Seq[Integer]], pt : ParameterTheory): Boolean = {

    val tmp = for (path <- all_paths) yield PathFormula(path, sfa, pt, SimpleAPI.spawnWithAssertions)
    tmp.contains(SimpleAPI.ProverStatus.Sat)

  }

  def isEmpty(sfa : SFA[Conjunction, ITerm], pt : ParameterTheory): Boolean = {

    val empti_form = EmptinessFormula(sfa,ConstructAllPaths(sfa), pt)
    println("All path formula... " + empti_form)
    !empti_form
  }






}

