

package seqSolver

import ap.Prover.Model
import ap.parser._
import ap.SimpleAPI
import ap.terfor.conjunctions.Conjunction
import seqSolver.automataIntern._
import automata.sfa.SFA
import automata.sfa.SFAEpsilon
import automata.sfa.SFAInputMove
import automata.sfa.SFAMove
import transducers.sft.{SFT, SFTInputMove, SFTMove}
import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}

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

  val autC = {
    import IExpression._
    val pt         = seqTheory.parameterTheory
    val Seq(p, q)  = seqTheory.parameterTheoryPars
    val Seq(c, c1) = seqTheory.parameterTheoryChars

    val interval1 = pt.FromFormula(i(p) + 5 <= c & c <= i(p) + 30)
    val interval2 = pt.FromFormula(i(p) - 35 <= c & c <= i(p) - 30)

    val transitions : Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 1, interval1),
      new SFAInputMove(1, 2, interval2)
    )

    val aut = SFA.MkSFA(transitions.asJava, 0,
      List(new Integer(2)).asJava,
      pt)
    new ParametricAutomaton(aut, pt)
  }

  val autD = {
    import IExpression._
    val pt         = seqTheory.parameterTheory
    val Seq(p, q)  = seqTheory.parameterTheoryPars
    val Seq(c, c1) = seqTheory.parameterTheoryChars

    val interval1 = pt.FromFormula(i(p) + 5 <= c & c <= i(p) + 30)
    val interval2 = pt.FromFormula(i(p) - 35 <= c & c <= i(p) - 30)

    val transitions : Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 1, interval1),
      new SFAInputMove(0, 2, interval1),
      new SFAInputMove(1, 3, interval2),
      new SFAInputMove(2, 3, interval2)
    )

    val aut = SFA.MkSFA(transitions.asJava, 0,
      List(new Integer(3)).asJava,
      pt)
    new ParametricAutomaton(aut, pt)
  }

  val autPaper1 = {
    import IExpression._
    val pt         = seqTheory.parameterTheory
    val Seq(p, q)  = seqTheory.parameterTheoryPars
    val Seq(c, c1) = seqTheory.parameterTheoryChars

    val interval1 = pt.FromFormula(i(p) === c)
    val interval2 = pt.FromFormula(c < i(p))

    val transitions : Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 0, Conjunction.TRUE),
      new SFAInputMove(0, 1, interval1),
      new SFAInputMove(1, 2, interval2),
      new SFAInputMove(2, 2, Conjunction.TRUE)
    )

    val aut = SFA.MkSFA(transitions.asJava, 0,
      List(new Integer(2)).asJava,
      pt)
    new ParametricAutomaton(aut, pt)
  }

  val autPaper2 = {
    import IExpression._
    val pt         = seqTheory.parameterTheory
    val Seq(p, q)  = seqTheory.parameterTheoryPars
    val Seq(c, c1) = seqTheory.parameterTheoryChars

    val interval1 = pt.FromFormula(i(p) === c)
    val interval2 = pt.FromFormula(c <= i(p))

    val transitions : Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 0, interval2),
      new SFAInputMove(0, 1, interval1),
      new SFAInputMove(1, 1, interval2)
    )

    val aut = SFA.MkSFA(transitions.asJava, 0,
      List(new Integer(1)).asJava,
      pt)
    new ParametricAutomaton(aut, pt)
  }

  val autPaper3 = {
    import IExpression._
    val pt         = seqTheory.parameterTheory
    val Seq(p, q)  = seqTheory.parameterTheoryPars
    val Seq(c, c1) = seqTheory.parameterTheoryChars

    val interval1 = pt.FromFormula(c === 1)
    val interval2 = pt.FromFormula(c === 2)
    val interval3 = pt.FromFormula(c === 3)
    val interval4 = pt.FromFormula(c === 5)
    val interval5 = pt.FromFormula(c === 4)

    val transitions : Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 1, interval1),
      new SFAInputMove(1, 2, interval2),
      new SFAInputMove(2, 3, interval3),
      new SFAInputMove(3, 4, interval4),
      new SFAInputMove(4, 5, interval5)
    )

    val aut = SFA.MkSFA(transitions.asJava, 0,
      List(new Integer(5)).asJava,
      pt)
    new ParametricAutomaton(aut, pt)
  }

  val increment10Transducer = {
    import IExpression._

    val pt         = seqTheory.parameterTheory
    val Seq(p, q)  = seqTheory.parameterTheoryPars
    val Seq(c, c1) = seqTheory.parameterTheoryChars

    val incrementFunction = c + 10
    val intervalTop = Conjunction.TRUE

    val transitions : Seq[pt.SFTMove] = List(
      new SFTInputMove(0,0,intervalTop , Seq(incrementFunction).asJava)
    )
    val finStates = new MHashMap[Integer, java.util.Set[java.util.List[ITerm]]]
    finStates.put(0, new MHashSet[java.util.List[ITerm]].asJava)

    val trans = SFT.MkSFT(transitions.asJava, 0, finStates.asJava, seqTheory.parameterTheory)
    new ParametricTransducer(trans, pt)
  }

  println("transducer: " + increment10Transducer)
  println("test1 " + increment10Transducer.preImage(autPaper3))
  val l = List(Int2ITerm(1),Int2ITerm(2),Int2ITerm(3),Int2ITerm(4),Int2ITerm(5),Int2ITerm(7))
  println("test2 " + increment10Transducer(l))

  val negativeToPositiveInts = {
    import IExpression._

    val pt         = seqTheory.parameterTheory
    val Seq(p, q)  = seqTheory.parameterTheoryPars
    val Seq(c, c1) = seqTheory.parameterTheoryChars

    val flip = c * -1
    val identity = ConstantTerm2ITerm(c)
    val intervalGreater = pt.FromFormula(c > 0)
    val intervalSmallerEqual = pt.FromFormula(c <= 0)

    val transitions : Seq[pt.SFTMove] = List(
      new SFTInputMove(0,0,intervalGreater , Seq(identity).asJava),
    new SFTInputMove(0,0,intervalSmallerEqual , Seq(flip).asJava)
    )
    val finStates = new MHashMap[Integer, java.util.Set[java.util.List[ITerm]]]
    finStates.put(0, new MHashSet[java.util.List[ITerm]].asJava)

    val trans = SFT.MkSFT(transitions.asJava, 0, finStates.asJava, seqTheory.parameterTheory)
    new ParametricTransducer(trans, pt)
  }
  println("transducer2: " + negativeToPositiveInts)
  println("test3 " + negativeToPositiveInts.preImage(autPaper3))
  val l2 = List(Int2ITerm(1),Int2ITerm(-2),Int2ITerm(3),Int2ITerm(4),Int2ITerm(-5),Int2ITerm(7))
  println("test4 " + negativeToPositiveInts(l))
  println("test5 " + negativeToPositiveInts(l2))

  val autAId = seqTheory.autDatabase.registerAut(autA)
  val autBId = seqTheory.autDatabase.registerAut(autB)
  val autCId = seqTheory.autDatabase.registerAut(autC)
  val autDId = seqTheory.autDatabase.registerAut(autD)

  val autP1Id = seqTheory.autDatabase.registerAut(autPaper1)
  val autP2Id = seqTheory.autDatabase.registerAut(autPaper2)
  val autP3Id = seqTheory.autDatabase.registerAut(autPaper3)

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(seqTheory)

    import seqTheory.{SeqSort, seq_in_re_id, seq_++, seq_empty}

    var s1 = createConstant("s1", SeqSort)
    val s2 = createConstant("s2", SeqSort)
    val s3 = createConstant("s3", SeqSort)
    // membership in parameterised automaton
    //!! (seq_in_re_id(s1, autP1Id))
    !! (seq_in_re_id(s1, autP3Id))
   // val l = (seq_++(s2,s3))
    //!! (l === s1)

    // global constraint on the parameters
    //!! (seqTheory.parameterTerms(0) >= 0)

    println(" res " + ???)
    println("s1: " + evalToTerm(s1))
    println("s2: " + evalToTerm(s2))
    println("s3: " + evalToTerm(s3))
  }

}
