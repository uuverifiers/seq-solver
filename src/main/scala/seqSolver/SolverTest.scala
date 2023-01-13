

package seqSolver

import ap.parser._
import ap.SimpleAPI
import seqSolver.automataIntern._
import automata.sfa.SFA
import automata.sfa.SFAEpsilon
import automata.sfa.SFAInputMove
import automata.sfa.SFAMove

import scala.collection.JavaConverters._

object SolverTest extends App {

  import IExpression._

  val seqTheory = new SeqTheory(Sort.Integer,
                                List(("p", Sort.Integer), ("q", Sort.Integer)))

  val autA = {
    import IExpression._
    val pt         = seqTheory.parameterTheory
    val Seq(p, q)  = seqTheory.parameterTheoryPars
    val Seq(c, c1) = seqTheory.parameterTheoryChars

    val interval = pt.FromFormula(i(p) <= c & c <= i(p) + 20)

    val transitions : Seq[pt.SFAMove] = List(
      new SFAEpsilon(0, 1),
      new SFAInputMove(0, 0, interval)
    )

    val aut = SFA.MkSFA(transitions.asJava, 0,
                        List(new Integer(0), new Integer(1)).asJava,
                        pt)
    new ParametricAutomaton(aut, pt)
  }

  val autB = {
    import IExpression._
    val pt         = seqTheory.parameterTheory
    val Seq(p, q)  = seqTheory.parameterTheoryPars
    val Seq(c, c1) = seqTheory.parameterTheoryChars

    val interval = pt.FromFormula(i(p) + 5 <= c & c <= i(p) + 30)

    val transitions : Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 1, interval)
    )

    val aut = SFA.MkSFA(transitions.asJava, 0,
      List(new Integer(1)).asJava,
      pt)
    new ParametricAutomaton(aut, pt)
  }

  val autAId = seqTheory.autDatabase.registerAut(autA)
  val autBId = seqTheory.autDatabase.registerAut(autB)

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(seqTheory)

    import seqTheory.{SeqSort, seq_in_re_id}

    val s = createConstant("s", SeqSort)

    // membership in parameterised automaton
    !! (seq_in_re_id(s, autBId))

    // global constraint on the parameters
    //!! (seqTheory.parameterTerms(0) >= 0)

    println(" res " + ???)
    println("partial model: " + partialModel)
  }

}
