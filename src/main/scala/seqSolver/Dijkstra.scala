package seqSolver

import ap.SimpleAPI
import ap.parser.IExpression.{ConstantTerm2ITerm, Int2ITerm, Sort, i}
import ap.parser.{IExpression, ITerm}
import ap.terfor.conjunctions.Conjunction
import automata.sfa.{SFA, SFAInputMove}
import seqSolver.automataIntern.{ParametricAutomaton, ParametricTransducer}
import transducers.sft.{SFT, SFTInputMove}

import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}
import scala.collection.JavaConverters._
object Dijkstra extends App {

  import IExpression._
  val seqTheory = new SeqTheory(Sort.Integer,
    List(("p1", Sort.Integer), ("p2", Sort.Integer), ("p3", Sort.Integer), ("p", Sort.Integer), ("k", Sort.Integer)))
  val pt = seqTheory.parameterTheory
  val Seq(c, c1) = seqTheory.parameterTheoryChars
  val Seq(p1, p2, p3, p, k) = seqTheory.parameterTheoryPars


  val l1 = {

    val transitions: Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 1, pt.FromFormula(c === i(p1))),
      new SFAInputMove(1, 2, pt.FromFormula(i(p1) === c)),
      new SFAInputMove(2, 2, pt.FromFormula(i(p1) === c)),

      new SFAInputMove(3, 3, pt.FromFormula(i(p1) === c)),
      new SFAInputMove(0, 3, pt.FromFormula(i(p1) === c)),
      new SFAInputMove(3, 4, pt.FromFormula(i(p2) === c & i(p1) =/= i(p2))),
      new SFAInputMove(4, 4, pt.FromFormula(i(p2) === c))
    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(2), new Integer(4)).asJava, pt)
    new ParametricAutomaton(aut, pt)
  }

  val l2 = {

    val transitions: Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 4, Conjunction.TRUE),
      new SFAInputMove(0, 1, pt.FromFormula(i(p2) === c)),
      new SFAInputMove(1, 1, pt.FromFormula(i(p2) === c)),

      new SFAInputMove(1, 2, pt.FromFormula(i(p2) === c & i(p1) =/= i(p2))),
      new SFAInputMove(2, 2, pt.FromFormula(i(p2) === c)),

      new SFAInputMove(2, 3, pt.FromFormula(i(p3) === c & i(p2) =/= i(p3))),
      new SFAInputMove(3, 3, Conjunction.TRUE)
    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(0), new Integer(3), new Integer(4)).asJava, pt)
    new ParametricAutomaton(aut, pt)
  }

  val t = {

    val copy = ConstantTerm2ITerm(c)
    val outputP = ConstantTerm2ITerm(p)
    val zero = Int2ITerm(0)
    val inc = copy + 1


    val transitions: Seq[pt.SFTMove] = List(
      new SFTInputMove(0, 1, pt.FromFormula(c < i(k) - 1 & c === p & c >= 0), List(inc).asJava),
      new SFTInputMove(0, 1, pt.FromFormula(c === i(k) - 1 & c === p & c >= 0), List(zero).asJava),
      new SFTInputMove(0, 3, Conjunction.TRUE, List(copy).asJava),
      new SFTInputMove(0, 4, pt.FromFormula(c === p), List(copy).asJava),

      new SFTInputMove(1, 1, Conjunction.TRUE, List(copy).asJava),
      new SFTInputMove(1, 2, pt.FromFormula(c === p), List(copy).asJava),

      new SFTInputMove(3, 3, Conjunction.TRUE, List(copy).asJava),
      new SFTInputMove(3, 4, pt.FromFormula(c === p), List(copy).asJava),

      new SFTInputMove(4, 5, pt.FromFormula(c =/= p), List(outputP).asJava),
      new SFTInputMove(5, 5, Conjunction.TRUE, List(copy).asJava)

    )
    val finStates = new MHashMap[Integer, java.util.Set[java.util.List[ITerm]]]
    finStates.put(2, new MHashSet[java.util.List[ITerm]].asJava)
    finStates.put(5, new MHashSet[java.util.List[ITerm]].asJava)
    val trans = SFT.MkSFT(transitions.asJava, 0, finStates.asJava, seqTheory.parameterTheory)
    new ParametricTransducer(trans, pt)
  }

  val autL1 = seqTheory.autDatabase.registerAut(l1)
  val autL2 = seqTheory.autDatabase.registerAut(l2)
  val transition = seqTheory.autDatabase.registerTrans(t)


  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(seqTheory)

    import seqTheory.{SeqSort, seq_in_re_id, seq_in_relation_id}

    var s1 = createConstant("s1", SeqSort)
    val s2 = createConstant("s2", SeqSort)
    // membership in parameterised automaton
    //!! (seq_in_re_id(s1, autP1Id))
    !!(seq_in_re_id(s1, autL1))
    !!(s2 === seq_in_relation_id(s1, transition))

    !!(seq_in_re_id(s2, autL2))
    //!! (seq_in_re_id(s1, autInv0))
    //!! (seq_in_re_id(s1, autPost))
    //!! (seq_in_re_id(s1, autNegInv0))
    // val l = (seq_++(s2,s3))
    //!! (l === s1)

    // global constraint on the parameters
    //!! (seqTheory.parameterTerms(0) >= 0)

    println(" res " + ???)
    /*    println("s1: " + evalToTerm(s1))
    println("s2: " + evalToTerm(s2))*/
  }
}
