
package seqSolver

import ap.api.SimpleAPI
import ap.types.Sort
import ap.parser._
import ap.terfor.conjunctions.Conjunction.collectQuantifiers
import automata.sfa.SFA
import automata.sfa.SFAEpsilon
import automata.sfa.SFAInputMove
import automata.sfa.SFAMove
import seqSolver.preop.ConcatPreOp

import scala.collection.JavaConverters._

object Main extends App {

  println("Testing Parameterised Automaton ...")

  val pt = ParameterTheory(Sort.Integer, List(Sort.Integer))

  // Words [p, (p+20)]*
  val autA = {
    import IExpression._

    val interval = pt.FromFormula(i(pt.parameters(0)) <= pt.charSymbol &
                                  pt.charSymbol <= i(pt.parameters(0)) + 20)
    println(pt.IsSatisfiable(interval))
    val transitions : Seq[pt.SFAMove] = List(
      new SFAEpsilon(0, 1),
      new SFAInputMove(0, 0, interval)
    )

    SFA.MkSFA(transitions.asJava, 0,
              List(new Integer(0), new Integer(1)).asJava,
              pt)
  }

  println("autA")
  println(autA)

  val autTop = {
    import IExpression._

    val interval = pt.FromFormula(i(pt.parameters(0)) <= pt.charSymbol &
      pt.charSymbol <= i(pt.parameters(0)) + 20)
    val transitions : Seq[pt.SFAMove] = List(
      new SFAEpsilon(0, 1),
      new SFAInputMove(0, 0, interval)
    )

    SFA.MkSFA(transitions.asJava, 0,
      List(new Integer(1), new Integer(1)).asJava,
      pt)
  }

  println("autTop")
  println(autTop)

  // Words [(p+5), (p+30)]
  val autB = {
    import IExpression._

    val interval = pt.FromFormula(i(pt.parameters(0)) + 5 <= pt.charSymbol &
                                  pt.charSymbol <= i(pt.parameters(0)) + 30)

    val transitions : Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 1, interval)
    )

    SFA.MkSFA(transitions.asJava, 0,
              List(new Integer(1)).asJava,
              pt)
  }

  println("autB")
  println(autB)

  // Words [(p+5), (p+30)]+
  val autC = SFA.star(autB, pt).concatenateWith(autB, pt).minimize(pt)

  println("autC")
  println(autC)

  // autA & autC

  val autD = autA.intersectionWith(autC, pt)

  println("autD")
  println(autD)

  // Automaton describing the empty language (transitions with
  // inconsistent guards p = 0, p = 1)

  val autE = {
    import IExpression._

    val interval = pt.FromFormula(i(pt.parameters(0)) + 5 <= pt.charSymbol &
                                  pt.charSymbol <= i(pt.parameters(0)) + 30)

    val transitions : Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 1, pt.FromFormula(i(pt.parameters(0)) === 0)),
      new SFAInputMove(1, 2, pt.FromFormula(i(pt.parameters(0)) === 1))
    )

    SFA.MkSFA(transitions.asJava, 0,
              List(new Integer(2)).asJava,
              pt)
  }

  println("autE")
  println(autE)

  val autF = autE.complement(pt)

  println("autF")
  println(autF)
  val autG = autA.complement(pt)
  val l = SFAUtilities()
  println("The automaton \n" + autC + "\nis empty: " + l.isEmpty(autC, pt))

  val concatTest = ConcatPreOp(List(List(),List()), autC, pt)
  for (t <- concatTest){
    println("\n")
    println(t)
    println("\n")
  }

}
