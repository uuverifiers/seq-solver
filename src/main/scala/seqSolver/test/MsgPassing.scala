package seqSolver.test

import ap.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
import ap.parser.{IExpression, ITerm}
import ap.terfor.conjunctions.Conjunction
import automata.sfa.{SFA, SFAInputMove, SFAEpsilon}
import seqSolver.SeqTheory
import seqSolver.automataIntern.ParametricAutomaton
import ap.theories.ADT

import scala.collection.JavaConverters._



object MsgPassing extends App {

  import IExpression._

  /**
   * Stores define the values of the two shared variables, x and y
   */
  val (storeSort, store, Seq(x, y)) =
    ADT.createRecordType("Store",
                         List(("x", Sort.Integer),
                              ("y", Sort.Integer)))

  val storeTheory = storeSort.asInstanceOf[ADT.ADTProxySort].adtTheory

  /**
   * Sequences of stores
   */
  val seqTheory = new SeqTheory(storeSort,
                                List(), // parameters
                                Seq(storeTheory))

  val pt = seqTheory.parameterTheory
  val Seq(c, c1) = seqTheory.parameterTheoryChars

  /**
   * Definition of the regular languages involved in the assertions.
   */

  def genAut(transitions : Seq[pt.SFAMove],
             accepting : Seq[Int]) : Int = {
    val aut = SFA.MkSFA(transitions.asJava,
                        0, (for (a <- accepting) yield new Integer(a)).asJava,
                        pt, false, false, false)
    val paut = new ParametricAutomaton(aut, pt)
    seqTheory.autDatabase.registerAut(paut)
  }

  // Language of non-empty words
  val nonEmpty =
    genAut(List(
             new SFAInputMove(0, 1, pt.FromFormula(true)),
             new SFAInputMove(1, 1, pt.FromFormula(true))
           ),
           List(1))

  // [ y != 1 ]
  val aut1 =
    genAut(List(
             new SFAInputMove(0, 1, pt.FromFormula(y(c) =/= 1)),
             new SFAInputMove(1, 1, pt.FromFormula(y(c) =/= 1))
           ),
           List(1))

  // [ x == 1 ]
  val aut2 =
    genAut(List(
             new SFAInputMove(0, 0, pt.FromFormula(x(c) === 1))
           ),
           List(0))

  // Complement of aut2
  val aut2Comp =
    genAut(List(
             new SFAInputMove(0, 0, pt.FromFormula(true)),
             new SFAInputMove(0, 1, pt.FromFormula(x(c) =/= 1)),
             new SFAInputMove(1, 1, pt.FromFormula(true))
           ),
           List(1))

  // [ y != 1 ]; [ x == 1 ]
  val aut3 =
    genAut(List(
             new SFAInputMove(0, 0, pt.FromFormula(y(c) =/= 1)),
             new SFAEpsilon(0, 1),
             new SFAInputMove(1, 1, pt.FromFormula(x(c) === 1))
           ),
           List(1))

  /*

   0 -A-> 0
   0 -!A & B-> 1
   1 -B-> 1

   0 -!A & !B-> 2
   1 -!B-> 2
   2 -true-> 2

   accepting 0, 1;

   */

  // Complement of aut3
  val aut3Comp =
    genAut(List(
             new SFAInputMove(0, 0, pt.FromFormula(y(c) =/= 1)),
             new SFAInputMove(0, 1, pt.FromFormula(y(c) === 1 & x(c) === 1)),
             new SFAInputMove(0, 2, pt.FromFormula(y(c) === 1 & x(c) =/= 1)),
             new SFAInputMove(1, 1, pt.FromFormula(x(c) === 1)),
             new SFAInputMove(1, 2, pt.FromFormula(x(c) =/= 1)),
             new SFAInputMove(2, 2, pt.FromFormula(true))
           ),
           List(2))

  // [ y != 1 ]; [ x == 1 ]; [ x == 1 ]
  val aut4 =
    genAut(List(
             new SFAInputMove(0, 0, pt.FromFormula(y(c) =/= 1)),
             new SFAEpsilon(0, 1),
             new SFAInputMove(1, 1, pt.FromFormula(x(c) === 1)),
             new SFAEpsilon(1, 2),
             new SFAInputMove(2, 2, pt.FromFormula(x(c) === 1))
           ),
           List(2))


  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._
    import seqTheory.{SeqSort, seq_in_re_id, seq_++}

    addTheory(seqTheory)

    val a    = createConstant("a", Sort.Integer)
    val b    = createConstant("b", Sort.Integer)
    val pot  = createConstant("pot", SeqSort)
    val pot2 = createConstant("pot2", SeqSort)
    val l    = createConstant("l", SeqSort)

    // only consider non-empty sequences of stores
    !! (seq_in_re_id(pot, nonEmpty))

    scope {
      // { T0 sees [y != 1] } ... { T2 sees [y != 1]; [ x == 1 ] }
      print("T2 valid Hoare triple 1 ... ")
      !! (seq_in_re_id(pot, aut1))
      ?? (!seq_in_re_id(pot, aut3Comp))
      println(???)
    }

    scope {
      // { T2 sees [y != 1]; [ x == 1 ] } ...LOAD... { a==1 => T2 sees [x==1] }
      print("T2 valid Hoare triple 2 ... ")

      // What exactly is the Hoare rule for LOAD in this setting?
      // Which checks are needed for lossiness?

      ?? (true)
      println(???)
    }

    scope {
      // Stability of { T2 sees [y != 1]; [ x == 1 ] } under STORE(x, 1)
      print("T2 stable assertion 1 ... ")
      !! (seq_in_re_id(pot, aut4))
      ?? (!seq_in_re_id(pot, aut3Comp))
      println(???)
    }

    scope {
      // Stability of { a==1 => T2 sees [ x == 1 ] } under STORE(x, 1)
      print("T2 stable assertion 2 ... ")
      // Probably not the right encoding: let's just say that the effect
      // of STORE is to append some elements to the T2-potential
      !! (a===1 ==> seq_in_re_id(pot, aut2))
      !! (seq_in_re_id(l, aut2))
      !! (pot2 === seq_++(pot, l))
      ?? (a===1 ==> !seq_in_re_id(pot2, aut2Comp))
      println(???)
    }

  }

}
