package seqSolver.test

import ap.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
import ap.parser.{IExpression, ITerm}
import ap.terfor.conjunctions.Conjunction
import automata.sfa.{SFA, SFAInputMove}
import seqSolver.SeqTheory
import seqSolver.automataIntern.{ParametricAutomaton, ParametricTransducer}
import transducers.sft.{SFT, SFTInputMove}

import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}
import scala.collection.JavaConverters._



object QuickSort {

  import IExpression._

  val seqTheory = new SeqTheory(Sort.Integer,
    List(("p", Sort.Integer)))
  val pt = seqTheory.parameterTheory
  val Seq(c, c1) = seqTheory.parameterTheoryChars
  val Seq(p) = seqTheory.parameterTheoryPars


  val inv = {

    val transitions: Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 0, Conjunction.TRUE),
      new SFAInputMove(0, 1, pt.FromFormula(i(p) === c)),
      new SFAInputMove(1, 1, Conjunction.TRUE)
    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(1)).asJava, pt)
    new ParametricAutomaton(aut, pt)
  }

  val negInv = {

    val transitions: Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 0, pt.FromFormula(i(p) =/= c)),
      new SFAInputMove(0, 1, pt.FromFormula(i(p) === c)),
      new SFAInputMove(1, 1, Conjunction.TRUE)
    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(0)).asJava, pt)
    new ParametricAutomaton(aut, pt)
  }


  val smallerP = {

    val transitions: Seq[pt.SFTMove] = List(

      new SFTInputMove(0, 0, pt.FromFormula(c < i(p)), List(ConstantTerm2ITerm(c)).asJava),
      new SFTInputMove(0, 0, pt.FromFormula(c >= i(p)), List().asJava)
    )
    val finStates = new MHashMap[Integer, java.util.Set[java.util.List[ITerm]]]
    finStates.put(0, new MHashSet[java.util.List[ITerm]].asJava)
    val trans = SFT.MkSFT(transitions.asJava, 0, finStates.asJava, seqTheory.parameterTheory)
    new ParametricTransducer(trans, pt)
  }
  val greaterP = {

    val transitions: Seq[pt.SFTMove] = List(

      new SFTInputMove(1, 1, pt.FromFormula(c >= i(p)), List(ConstantTerm2ITerm(c)).asJava),
      new SFTInputMove(1, 1, pt.FromFormula(c < i(p)), List().asJava),
      new SFTInputMove(0, 0, pt.FromFormula(c < i(p)), List().asJava),
      new SFTInputMove(0, 1, pt.FromFormula(c === i(p)), List().asJava)
    )
    val finStates = new MHashMap[Integer, java.util.Set[java.util.List[ITerm]]]
    finStates.put(0, new MHashSet[java.util.List[ITerm]].asJava)
    finStates.put(1, new MHashSet[java.util.List[ITerm]].asJava)
    val trans = SFT.MkSFT(transitions.asJava, 0, finStates.asJava, seqTheory.parameterTheory)
    new ParametricTransducer(trans, pt)
  }

  val equalP = {

    val transitions: Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 1, pt.FromFormula(c === i(p)))
    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(1)).asJava, pt)
    new ParametricAutomaton(aut, pt)
  }


  val autInv = seqTheory.autDatabase.registerAut(inv)
  val autNegInv = seqTheory.autDatabase.registerAut(negInv)
  val smallerPId = seqTheory.autDatabase.registerTrans(smallerP)
  val greaterPId = seqTheory.autDatabase.registerTrans(greaterP)
  val equalPId = seqTheory.autDatabase.registerAut(equalP)

  def run(enableAssertions : Boolean) : Boolean = {
    SimpleAPI.withProver(enableAssert = enableAssertions) { p =>
      import p._

      addTheory(seqTheory)

      import seqTheory.{SeqSort, seq_++, seq_in_re_id, seq_in_relation_id}

      val s1 = createConstant("s1", SeqSort)
      val s2 = createConstant("s2", SeqSort)
      val s3 = createConstant("s3", SeqSort)
      val s4 = createConstant("s4", SeqSort)

      !!(seq_in_re_id(s1, autInv))
      !!(seq_in_re_id(s2, equalPId))

      val l = (seq_++(seq_in_relation_id(s1, smallerPId), s2))

      !!(s3 === l)

      val l1 = (seq_++(s3, seq_in_relation_id(s1, greaterPId)))

      !!(s4 === l1)

      !!(seq_in_re_id(l1, autNegInv))
      return ??? == ProverStatus.Unsat

    }
  }


}
