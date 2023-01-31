package seqSolver.test

import ap.SimpleAPI
import ap.parser.IExpression.{ConstantTerm2ITerm, Sort, eqZero, i}
import ap.parser.{IFormula, ITerm}
import ap.terfor.conjunctions.Conjunction
import ap.theories.ADT
import automata.sfa.{SFA, SFAInputMove}
import seqSolver.SeqTheory
import seqSolver.automataIntern.{ParametricAutomaton, ParametricTransducer}
import transducers.sft.{SFT, SFTEpsilon, SFTInputMove}
import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}
import scala.collection.JavaConverters._
import ap.parser.IExpression._

object BakeryTest extends App {


  val (stateSort, Seq(enteringTrue, choosingNumber, enteringFalse, checkingEntering, inSection)) =
    ADT.createEnumType("State", List("enteringTrue", "choosingNumber", "enteringFalse", "checkingEntering", "inSection"))

  val (processSort, process, Seq(state, entering, number)) =
    ADT.createRecordType("Process",
      List(("state", stateSort),
        ("entering", Sort.Bool),
        ("number", Sort.Integer)))


  val theoryADT = processSort.asInstanceOf[ADT.ADTProxySort].adtTheory
  val theoryEnum = stateSort.asInstanceOf[ADT.ADTProxySort].adtTheory


  def isEntering(t: ITerm): IFormula = eqZero(entering(t))

  val seqTheory = new SeqTheory(processSort,
    List(("p", Sort.Integer), ("q", Sort.Integer)), Seq(theoryADT, theoryEnum))
  val pt = seqTheory.parameterTheory
  val Seq(c, c1) = seqTheory.parameterTheoryChars
  val Seq(p, q) = seqTheory.parameterTheoryPars

  val l: ITerm = process(enteringTrue, 1, 0)


  println("init")
  val initialAut = {

    val transitions: Seq[pt.SFAMove] = List(

      new SFAInputMove(0, 0, pt.FromFormula(number(c) === 0 & isEntering(c) & state(c) === enteringTrue))

    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(0)).asJava, pt, false, false, false)
    new ParametricAutomaton(aut, pt)

  }
  println("trabs")
  val transitionsTransducer = {

    val enteringTrueGuard = pt.FromFormula(state(c) === enteringTrue)
    val choosingNumberGuard = pt.FromFormula(state(c) === choosingNumber)
    val enteringFalseGuard = pt.FromFormula(state(c) === enteringFalse)
    val inSectionGuard = pt.FromFormula(state(c) === inSection)
    val checkingEnteringGuard = pt.FromFormula(state(c) === checkingEntering)

    val isEnteringGuard = pt.FromFormula(isEntering(c))
    val isNotEnteringGuard = pt.FromFormula(!isEntering(c))
    val copyGuard = pt.FromFormula(number(c) <= p)
    val copyGuardEnter = pt.FromFormula((number(c) === i(0) | number(c) > p) & !isEntering(c))
    val parameterGreaterZero = pt.FromFormula(i(0) <= p)
    val inSectionGuard2 = pt.FromFormula(i(0) === p & state(c) === checkingEntering)


    val copyLetter = Seq(ConstantTerm2ITerm(c)).asJava

    val enteringTrueChooseNumber: ITerm = process(choosingNumber, entering(c), number(c))
    val enteringFalseInc: ITerm = process(enteringFalse, entering(c), p + 1)
    val checkingEnteringFunc: ITerm = process(checkingEntering, 1 - entering(c), number(c))
    val inSectionFuncNeg: ITerm = process(inSection, 1 - entering(c), number(c))
    val inSectionFuncPos: ITerm = process(inSection, entering(c), number(c))
    val transitions: Seq[pt.SFTMove] = List(

      new SFTEpsilon(0, 1, List().asJava),
      new SFTInputMove(1, 1, Conjunction.TRUE, copyLetter),
      new SFTInputMove(1, 2, pt.MkAnd(enteringTrueGuard, isNotEnteringGuard), Seq(enteringTrueChooseNumber).asJava),
      new SFTInputMove(2, 2, Conjunction.TRUE, copyLetter),
      new SFTEpsilon(0, 3, List().asJava),
      new SFTInputMove(3, 3, copyGuard, copyLetter),
      new SFTInputMove(3, 4, pt.MkAnd(Seq(choosingNumberGuard, copyGuard, parameterGreaterZero).asJava), Seq(enteringFalseInc).asJava),
      new SFTInputMove(4, 4, copyGuard, copyLetter),
      new SFTEpsilon(0, 5, List().asJava),
      new SFTInputMove(5, 5, Conjunction.TRUE, copyLetter),
      new SFTInputMove(5, 6, pt.MkAnd(Seq(enteringFalseGuard, isEnteringGuard).asJava), Seq(checkingEnteringFunc).asJava),
      new SFTInputMove(6, 6, Conjunction.TRUE, copyLetter),
      new SFTEpsilon(0, 7, List().asJava),
      new SFTInputMove(7, 7, copyGuardEnter, copyLetter),
      new SFTInputMove(7, 8, inSectionGuard2, Seq(inSectionFuncNeg).asJava),
      new SFTInputMove(7, 8, inSectionGuard2, Seq(inSectionFuncPos).asJava),
      new SFTInputMove(8, 8, copyGuardEnter, copyLetter)
    )

    val finStates = new MHashMap[Integer, java.util.Set[java.util.List[ITerm]]]
    finStates.put(2, new MHashSet[java.util.List[ITerm]].asJava)
    finStates.put(4, new MHashSet[java.util.List[ITerm]].asJava)
    finStates.put(6, new MHashSet[java.util.List[ITerm]].asJava)
    finStates.put(8, new MHashSet[java.util.List[ITerm]].asJava)
    val trans = SFT.MkSFT(transitions.asJava, 0, finStates.asJava, pt)
    new ParametricTransducer(trans, pt)
  }

  println("inv0")
  val inv0 = {

    val transitions: Seq[pt.SFAMove] = List(

      new SFAInputMove(0, 0, pt.FromFormula(number(c) >= 0))

    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(0)).asJava, pt)
    new ParametricAutomaton(aut, pt)

  }
  println("neginv0")
  val negInv0 = {

    val transitions: Seq[pt.SFAMove] = List(

      new SFAInputMove(0, 0, Conjunction.TRUE),
      new SFAInputMove(0, 1, pt.FromFormula(number(c) < 0)),
      new SFAInputMove(1, 1, Conjunction.TRUE)

    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(1)).asJava, pt)
    new ParametricAutomaton(aut, pt)

  }
  println("inv1")
  val inv1 = {


    val transitions: Seq[pt.SFAMove] = List(

      new SFAInputMove(0, 0, pt.FromFormula(state(c) =/= inSection & (number(c) > p | number(c) === 0)))

    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(0)).asJava, pt, false, false, false)
    new ParametricAutomaton(aut, pt)

  }
  println("neginv1")
  val negInv1 = {


    val transitions: Seq[pt.SFAMove] = List(

      new SFAInputMove(0, 0, Conjunction.TRUE),
      new SFAInputMove(0, 1, pt.FromFormula((number(c) === p & p > 0))),
      new SFAInputMove(1, 1, Conjunction.TRUE),
      new SFAInputMove(1, 2, pt.FromFormula((number(c) > p & state(c) === inSection))),
      new SFAInputMove(0, 3, pt.FromFormula((number(c) > p & state(c) === inSection))),
      new SFAInputMove(3, 3, Conjunction.TRUE),
      new SFAInputMove(3, 4, pt.FromFormula((number(c) === p & p > 0))),
      new SFAInputMove(4, 4, Conjunction.TRUE),
      new SFAInputMove(2, 2, Conjunction.TRUE)
    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(2), new Integer(4)).asJava, pt, false, false, false)
    new ParametricAutomaton(aut, pt)

  }
  println("neginv2")
  val negInv2 = {
    val transitions: Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 0, Conjunction.TRUE),
      new SFAInputMove(0, 1, pt.FromFormula(state(c) === checkingEntering | state(c) === enteringFalse & (number(c) === 0))),
      new SFAInputMove(1, 1, Conjunction.TRUE)
    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(0)).asJava, pt)
    new ParametricAutomaton(aut, pt)

  }
  println("inv2")
  val inv2 = {
    val transitions: Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 0, pt.FromFormula(state(c) === checkingEntering | state(c) === enteringFalse ==> (number(c) > 0)))
    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(0)).asJava, pt)
    new ParametricAutomaton(aut, pt)

  }
  println("inv3")
  val inv3 = {
    val transitions: Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 0, pt.FromFormula(state(c) =/= inSection)),
      new SFAInputMove(0, 1, Conjunction.TRUE),
      new SFAInputMove(1, 1, pt.FromFormula(state(c) =/= inSection))
    )
    val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(1)).asJava, pt)
    new ParametricAutomaton(aut, pt)

  }
  println("neginv3")
  val negInv3 = {
    val transitions: Seq[pt.SFAMove] = List(
      new SFAInputMove(0, 0, Conjunction.TRUE),
      new SFAInputMove(0, 1, pt.FromFormula(state(c) === inSection)),
      new SFAInputMove(1, 1, Conjunction.TRUE),
      new SFAInputMove(1, 2, pt.FromFormula(state(c) === inSection)),
      new SFAInputMove(2, 2, Conjunction.TRUE)
    )
    val aut = SFA.MkSFA(transitions.asJava, 2, List(new Integer(0)).asJava, pt)
    new ParametricAutomaton(aut, pt)

  }


  val autInit = seqTheory.autDatabase.registerAut(initialAut)
  val autInv0 = seqTheory.autDatabase.registerAut(inv0)
  val autNegInv0 = seqTheory.autDatabase.registerAut(negInv0)
  val transId = seqTheory.autDatabase.registerTrans(transitionsTransducer)

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(seqTheory)

    import seqTheory.{SeqSort, seq_in_re_id}

    var s1 = createConstant("s1", SeqSort)
    val s2 = createConstant("s2", SeqSort)
    // membership in parameterised automaton
    //!! (seq_in_re_id(s1, autP1Id))
    !!(seq_in_re_id(s1, autInit))
    // !! (seq_in_re_id(s1, autInv0))
    //!! (seq_in_re_id(seq_in_relation_id(s1, transId), autNegInv0))
    //!! (seq_in_re_id(s1, autInv0))
    //!! (seq_in_re_id(s1, autPost))
    //!! (seq_in_re_id(s1, autNegInv0))
    // val l = (seq_++(s2,s3))
    //!! (l === s1)

    // global constraint on the parameters
    //!! (seqTheory.parameterTerms(0) >= 0)

    println(" res " + ???)
    println("s1: " + evalToTerm(s1))
    println("s2: " + evalToTerm(s2))
  }
}
