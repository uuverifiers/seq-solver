package seqSolver
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.theories.Theory
import ap.parser.{IConstant, IFormula, ITerm}
import ap.types.Sort
import ap.terfor.{ConstantTerm, Term}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import automata.sfa.{SFA, SFAMove}

import java.util.Collection
import java.util
import scala.collection.mutable
import scala.collection.mutable.Stack
import scala.collection.JavaConverters._

object SFAUtilities {
  def apply(): SFAUtilities = {
    new SFAUtilities
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
        val test = sfa.getInputMovesFrom(last).asScala
        val test2 = test.last.guard

        val successors_transitions  = sfa.getTransitionsFrom(last).asScala
        val successors = (for (n <- successors_transitions) yield n.to)
        println("l is ", successors)
        for (succ <- successors) {
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

  def PathFormula(path : Seq[Integer], sfa : SFA[Conjunction, ITerm], pt : ParameterTheory): Conjunction = {

    var res = Seq[Conjunction]()
    for (i <- 0 until path.length-1){
      println("Index", i)
      println("Node", path(i))
      println("trans", sfa.getInputMovesFrom(path(i)))
      val _tmp1 = sfa.getInputMovesFrom(path(i))
      for (tmp <- _tmp1.asScala){
        if (tmp.to == path(i+1)){
          //TODO more than one transition can happen?
          println("From", tmp.from, " to ", tmp.to, "guard", tmp.guard)
          res ++= Seq(tmp.guard)
        }
        // TODO handle no guard and epsilon?
      }
    }
    println(res)
    println(pt.MkAnd(res.asJavaCollection))
    pt.MkAnd(res.asJavaCollection)
  }

  def EmptinessFormula(sfa : SFA[Conjunction, ITerm], all_paths: Set[Seq[Integer]], pt : ParameterTheory): Conjunction = {
    val tmp = for (path <- all_paths) yield PathFormula(path, sfa, pt)
    val res = pt.MkOr(tmp.asJavaCollection)
    res
  }

  def isEmpty(sfa : SFA[Conjunction, ITerm], pt : ParameterTheory): Boolean = {
    !pt.IsSatisfiable(EmptinessFormula(sfa,ConstructAllPaths(sfa), pt))
  }

}

object Path{
  def apply(path : Seq[Integer]): Path = {
    new Path(path)
  }
}

class Path(val path : Seq[Integer]){
  val pat = path
}


