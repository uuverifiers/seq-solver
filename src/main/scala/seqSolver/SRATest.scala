

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
import seqSolver.SolverTest.seqTheory
import seqSolver.automataIntern.ParametricAutomaton.reverseAut
import transducers.sft.{SFT, SFTInputMove, SFTMove}

import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}
import scala.collection.JavaConverters._
import scala.language.postfixOps

object SRATest extends App {

  import IExpression._

  val seqTheory = new SeqTheory(Sort.Integer,
    List(("p0", Sort.Integer), ("p1", Sort.Integer),("p2", Sort.Integer),("p3", Sort.Integer),("p4", Sort.Integer),("p5", Sort.Integer),("p6", Sort.Integer),("p7", Sort.Integer),("p8", Sort.Integer),("p9", Sort.Integer)))

  val pt = seqTheory.parameterTheory
  val Seq(p0, p1, p2, p3, p4, p5, p6, p7, p8, p9)  = seqTheory.parameterTheoryPars
  val Seq(c, c1) = seqTheory.parameterTheoryChars
  val num = pt.FromFormula(i(48) <= c & c <= i(57))
  val dot = pt.FromFormula(i(46) === ConstantTerm2ITerm(c))
  val space = pt.FromFormula(i(32) === ConstantTerm2ITerm(c))
  val lower_alpha = pt.FromFormula(i(97) <= c & c <= i(122))
  val upper_alpha = pt.FromFormula(i(65) <= c & c <= i(90))
  val alpha = pt.MkOr(lower_alpha, upper_alpha)
  val alpha_num = Conjunction.disj(Seq(num, lower_alpha, upper_alpha), pt.order)
  val backslash = pt.FromFormula(i(92) === ConstantTerm2ITerm(c))
  val colon = pt.FromFormula(i(58) === ConstantTerm2ITerm(c))
  val small_s = pt.FromFormula(i(115) === ConstantTerm2ITerm(c))
  val small_d = pt.FromFormula(i(100) === ConstantTerm2ITerm(c))
  val small_p = pt.FromFormula(i(112) === ConstantTerm2ITerm(c))
  val big_C = pt.FromFormula(i(67) === c)
  val big_L = pt.FromFormula(i(76) === c)
  val big_D = pt.FromFormula(i(68) === c)
  val not_space = pt.MkNot(space)


  def getIP2PacketParser() : ParametricAutomaton = {
    val autGetIP2PacketParser = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, small_s),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(num, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, num),
        new SFAInputMove(5, 6, dot),
        new SFAInputMove(6, 7, num),
        new SFAInputMove(7, 8, num),
        new SFAInputMove(8, 9, num),
        new SFAInputMove(9, 10, dot),
        new SFAInputMove(10, 11, num),
        new SFAInputMove(11, 12, num),
        new SFAInputMove(12, 13, num),
        new SFAInputMove(13, 14, dot),
        new SFAInputMove(14, 15, num),
        new SFAInputMove(15, 16, num),
        new SFAInputMove(16, 17, num),
        new SFAInputMove(17, 18, space),
        new SFAInputMove(18, 19, pt.MkOr(alpha_num, colon)),
        new SFAInputMove(19, 20, small_d),
        new SFAInputMove(20, 21, colon),
        new SFAInputMove(21, 22, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(22, 23, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(23, 24, num),
        new SFAInputMove(24, 25, dot),
        new SFAInputMove(25, 26, num),
        new SFAInputMove(26, 27, num),
        new SFAInputMove(27, 28, num),
        new SFAInputMove(28, 29, dot),
        new SFAInputMove(29, 30, num),
        new SFAInputMove(30, 31, num),
        new SFAInputMove(31, 32, num),
        new SFAInputMove(32, 33, dot),
        new SFAInputMove(33, 34, num),
        new SFAInputMove(34, 35, num),
        new SFAInputMove(35, 36, num),
        new SFAInputMove(36, 37, space),
        new SFAInputMove(37, 37, pt.MkOr(alpha_num, colon)),
        new SFAInputMove(37, 38, space),
        new SFAInputMove(38, 39, small_p),
        new SFAInputMove(39, 40, colon),
        new SFAInputMove(40, 41, backslash),
        new SFAInputMove(41, 42, alpha_num),
        new SFAInputMove(42, 42, alpha_num),
        new SFAInputMove(42, 43, backslash)
      )

      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(43)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    autGetIP2PacketParser
  }

  def getIP3PacketParser: ParametricAutomaton = {
    val autGetIP3PacketParser = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, small_s),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(num, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(num, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, dot),
        new SFAInputMove(6, 7, num),
        new SFAInputMove(7, 8, num),
        new SFAInputMove(8, 9, num),
        new SFAInputMove(9, 10, dot),
        new SFAInputMove(10, 11, num),
        new SFAInputMove(11, 12, num),
        new SFAInputMove(12, 13, num),
        new SFAInputMove(13, 14, dot),
        new SFAInputMove(14, 15, num),
        new SFAInputMove(15, 16, num),
        new SFAInputMove(16, 17, num),
        new SFAInputMove(17, 18, space),
        new SFAInputMove(18, 19, pt.MkOr(alpha_num, colon)),
        new SFAInputMove(19, 20, small_d),
        new SFAInputMove(20, 21, colon),
        new SFAInputMove(21, 22, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(22, 23, pt.MkAnd(num, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(23, 24, pt.MkAnd(num, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(24, 25, dot),
        new SFAInputMove(25, 26, num),
        new SFAInputMove(26, 27, num),
        new SFAInputMove(27, 28, num),
        new SFAInputMove(28, 29, dot),
        new SFAInputMove(29, 30, num),
        new SFAInputMove(30, 31, num),
        new SFAInputMove(31, 32, num),
        new SFAInputMove(32, 33, dot),
        new SFAInputMove(33, 34, num),
        new SFAInputMove(34, 35, num),
        new SFAInputMove(35, 36, num),
        new SFAInputMove(36, 37, space),
        new SFAInputMove(37, 37, pt.MkOr(alpha_num, colon)),
        new SFAInputMove(37, 38, space),
        new SFAInputMove(38, 39, small_p),
        new SFAInputMove(39, 40, colon),
        new SFAInputMove(40, 41, backslash),
        new SFAInputMove(41, 42, alpha_num),
        new SFAInputMove(42, 42, alpha_num),
        new SFAInputMove(42, 43, backslash)
      )

      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(43)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    autGetIP3PacketParser
  }

  def getIP4PacketParser: ParametricAutomaton = {
    val autGetIP4PacketParser = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, small_s),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(num, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(num, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, dot),
        new SFAInputMove(6, 7, pt.MkAnd(num, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(7, 8, num),
        new SFAInputMove(8, 9, num),
        new SFAInputMove(9, 10, dot),
        new SFAInputMove(10, 11, num),
        new SFAInputMove(11, 12, num),
        new SFAInputMove(12, 13, num),
        new SFAInputMove(13, 14, dot),
        new SFAInputMove(14, 15, num),
        new SFAInputMove(15, 16, num),
        new SFAInputMove(16, 17, num),
        new SFAInputMove(17, 18, space),
        new SFAInputMove(18, 19, pt.MkOr(alpha_num, colon)),
        new SFAInputMove(19, 20, small_d),
        new SFAInputMove(20, 21, colon),
        new SFAInputMove(21, 22, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(22, 23, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(23, 24, pt.MkAnd(num, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(24, 25, dot),
        new SFAInputMove(25, 26, pt.MkAnd(num, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(26, 27, num),
        new SFAInputMove(27, 28, num),
        new SFAInputMove(28, 29, dot),
        new SFAInputMove(29, 30, num),
        new SFAInputMove(30, 31, num),
        new SFAInputMove(31, 32, num),
        new SFAInputMove(32, 33, dot),
        new SFAInputMove(33, 34, num),
        new SFAInputMove(34, 35, num),
        new SFAInputMove(35, 36, num),
        new SFAInputMove(36, 37, space),
        new SFAInputMove(37, 37, pt.MkOr(alpha_num, colon)),
        new SFAInputMove(37, 38, space),
        new SFAInputMove(38, 39, small_p),
        new SFAInputMove(39, 40, colon),
        new SFAInputMove(40, 41, backslash),
        new SFAInputMove(41, 42, alpha_num),
        new SFAInputMove(42, 42, alpha_num),
        new SFAInputMove(42, 43, backslash)
      )

      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(43)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    autGetIP4PacketParser
  }


  def getIP6PacketParser: ParametricAutomaton = {
    val autGetIP6PacketParser = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, small_s),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(num, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(num, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, dot),
        new SFAInputMove(6, 7, pt.MkAnd(num, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(7, 8, pt.MkAnd(num, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(8, 9, pt.MkAnd(num, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(9, 10, dot),
        new SFAInputMove(10, 11, num),
        new SFAInputMove(11, 12, num),
        new SFAInputMove(12, 13, num),
        new SFAInputMove(13, 14, dot),
        new SFAInputMove(14, 15, num),
        new SFAInputMove(15, 16, num),
        new SFAInputMove(16, 17, num),
        new SFAInputMove(17, 18, space),
        new SFAInputMove(18, 19, pt.MkOr(alpha_num, colon)),
        new SFAInputMove(19, 20, small_d),
        new SFAInputMove(20, 21, colon),
        new SFAInputMove(21, 22, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(22, 23, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(23, 24, pt.MkAnd(num, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(24, 25, dot),
        new SFAInputMove(25, 26, pt.MkAnd(num, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(26, 27, pt.MkAnd(num, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(27, 28, pt.MkAnd(num, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(28, 29, dot),
        new SFAInputMove(29, 30, num),
        new SFAInputMove(30, 31, num),
        new SFAInputMove(31, 32, num),
        new SFAInputMove(32, 33, dot),
        new SFAInputMove(33, 34, num),
        new SFAInputMove(34, 35, num),
        new SFAInputMove(35, 36, num),
        new SFAInputMove(36, 37, space),
        new SFAInputMove(37, 37, pt.MkOr(alpha_num, colon)),
        new SFAInputMove(37, 38, space),
        new SFAInputMove(38, 39, small_p),
        new SFAInputMove(39, 40, colon),
        new SFAInputMove(40, 41, backslash),
        new SFAInputMove(41, 42, alpha_num),
        new SFAInputMove(42, 42, alpha_num),
        new SFAInputMove(42, 43, backslash)
      )

      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(43)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    autGetIP6PacketParser
  }

  def getIP9PacketParser: ParametricAutomaton = {
    val autGetIP9PacketParser = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, small_s),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(num, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(num, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, dot),
        new SFAInputMove(6, 7, pt.MkAnd(num, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(7, 8, pt.MkAnd(num, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(8, 9, pt.MkAnd(num, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(9, 10, dot),
        new SFAInputMove(10, 11, pt.MkAnd(num, pt.FromFormula(c === i(p6)))),
        new SFAInputMove(11, 12, pt.MkAnd(num, pt.FromFormula(c === i(p7)))),
        new SFAInputMove(12, 13, pt.MkAnd(num, pt.FromFormula(c === i(p8)))),
        new SFAInputMove(13, 14, dot),
        new SFAInputMove(14, 15, num),
        new SFAInputMove(15, 16, num),
        new SFAInputMove(16, 17, num),
        new SFAInputMove(17, 18, space),
        new SFAInputMove(18, 19, pt.MkOr(alpha_num, colon)),
        new SFAInputMove(19, 20, small_d),
        new SFAInputMove(20, 21, colon),
        new SFAInputMove(21, 22, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(22, 23, pt.MkAnd(num, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(23, 24, pt.MkAnd(num, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(24, 25, dot),
        new SFAInputMove(25, 26, pt.MkAnd(num, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(26, 27, pt.MkAnd(num, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(27, 28, pt.MkAnd(num, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(28, 29, dot),
        new SFAInputMove(29, 30, pt.MkAnd(num, pt.FromFormula(c === i(p6)))),
        new SFAInputMove(30, 31, pt.MkAnd(num, pt.FromFormula(c === i(p7)))),
        new SFAInputMove(31, 32, pt.MkAnd(num, pt.FromFormula(c === i(p8)))),
        new SFAInputMove(32, 33, dot),
        new SFAInputMove(33, 34, num),
        new SFAInputMove(34, 35, num),
        new SFAInputMove(35, 36, num),
        new SFAInputMove(36, 37, space),
        new SFAInputMove(37, 37, pt.MkOr(alpha_num, colon)),
        new SFAInputMove(37, 38, space),
        new SFAInputMove(38, 39, small_p),
        new SFAInputMove(39, 40, colon),
        new SFAInputMove(40, 41, backslash),
        new SFAInputMove(41, 42, alpha_num),
        new SFAInputMove(42, 42, alpha_num),
        new SFAInputMove(42, 43, backslash)
      )

      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(43)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    autGetIP9PacketParser
  }

  def getProductParserC2 : ParametricAutomaton = {
    val prC2 = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, big_C),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, space),
        new SFAInputMove(5, 6, big_L),
        new SFAInputMove(6, 7, colon),
        new SFAInputMove(7, 8, alpha_num),
        new SFAInputMove(8, 9, space),
        new SFAInputMove(9, 10, big_D),
        new SFAInputMove(10, 11, colon),
        new SFAInputMove(11, 12, alpha),
        new SFAInputMove(12, 12, alpha),
        new SFAInputMove(12, 13, space),
        new SFAInputMove(13, 14, big_C),
        new SFAInputMove(14, 15, colon),
        new SFAInputMove(15, 16, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(16, 17, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(17, 18, space),
        new SFAInputMove(18, 19, big_L),
        new SFAInputMove(19, 20, colon),
        new SFAInputMove(20, 21, alpha_num),
        new SFAInputMove(21, 22, space),
        new SFAInputMove(22, 23, big_D),
        new SFAInputMove(23, 24, colon),
        new SFAInputMove(24, 25, alpha),
        new SFAInputMove(25, 25, alpha),
        new SFAInputMove(25, 13, space)

      )



      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(25)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    prC2
  }

  def getProductParserCL2 : ParametricAutomaton = {
    val prCL2 = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, big_C),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, space),
        new SFAInputMove(5, 6, big_L),
        new SFAInputMove(6, 7, colon),
        new SFAInputMove(7, 8, pt.MkAnd(alpha_num, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(8, 9, space),
        new SFAInputMove(9, 10, big_D),
        new SFAInputMove(10, 11, colon),
        new SFAInputMove(11, 12, alpha),
        new SFAInputMove(12, 12, alpha),
        new SFAInputMove(12, 13, space),
        new SFAInputMove(13, 14, big_C),
        new SFAInputMove(14, 15, colon),
        new SFAInputMove(15, 16, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(16, 17, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(17, 18, space),
        new SFAInputMove(18, 19, big_L),
        new SFAInputMove(19, 20, colon),
        new SFAInputMove(20, 21, pt.MkAnd(alpha_num, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(21, 22, space),
        new SFAInputMove(22, 23, big_D),
        new SFAInputMove(23, 24, colon),
        new SFAInputMove(24, 25, alpha),
        new SFAInputMove(25, 25, alpha),
        new SFAInputMove(25, 13, space)

      )



      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(25)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    prCL2
  }

  def getProductParserC3 : ParametricAutomaton = {
    val prC3 = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, big_C),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, space),
        new SFAInputMove(6, 7, big_L),
        new SFAInputMove(7, 8, colon),
        new SFAInputMove(8, 9, alpha_num),
        new SFAInputMove(9, 10, space),
        new SFAInputMove(10, 11, big_D),
        new SFAInputMove(11, 12, colon),
        new SFAInputMove(12, 13, alpha),
        new SFAInputMove(13, 13, alpha),
        new SFAInputMove(13, 14, space),
        new SFAInputMove(14, 15, big_C),
        new SFAInputMove(15, 16, colon),
        new SFAInputMove(16, 17, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(17, 18, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(18, 19, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(19, 20, space),
        new SFAInputMove(20, 21, big_L),
        new SFAInputMove(21, 22, colon),
        new SFAInputMove(22, 23, alpha_num),
      new SFAInputMove(23, 24, space),
      new SFAInputMove(24, 25, big_D),
      new SFAInputMove(25, 26, colon),
      new SFAInputMove(26, 27, alpha),
      new SFAInputMove(27, 27, alpha),
      new SFAInputMove(27, 14, space)

      )



      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(27)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    prC3
  }

  def getProductParserCL3 : ParametricAutomaton = {
    val prCL3 = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, big_C),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, space),
        new SFAInputMove(6, 7, big_L),
        new SFAInputMove(7, 8, colon),
        new SFAInputMove(8, 9, pt.MkAnd(alpha_num, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(9, 10, space),
        new SFAInputMove(10, 11, big_D),
        new SFAInputMove(11, 12, colon),
        new SFAInputMove(12, 13, alpha),
        new SFAInputMove(13, 13, alpha),
        new SFAInputMove(13, 14, space),
        new SFAInputMove(14, 15, big_C),
        new SFAInputMove(15, 16, colon),
        new SFAInputMove(16, 17, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(17, 18, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(18, 19, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(19, 20, space),
        new SFAInputMove(20, 21, big_L),
        new SFAInputMove(21, 22, colon),
        new SFAInputMove(22, 23, pt.MkAnd(alpha_num, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(23, 24, space),
        new SFAInputMove(24, 25, big_D),
        new SFAInputMove(25, 26, colon),
        new SFAInputMove(26, 27, alpha),
        new SFAInputMove(27, 27, alpha),
        new SFAInputMove(27, 14, space)

      )



      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(27)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    prCL3
  }

  def getProductParserC4 : ParametricAutomaton = {
    val prC4 = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, big_C),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(6, 7, space),
        new SFAInputMove(7, 8, big_L),
        new SFAInputMove(8, 9, colon),
        new SFAInputMove(9, 10, alpha_num),
        new SFAInputMove(10, 11, space),
        new SFAInputMove(11, 12, big_D),
        new SFAInputMove(12, 13, colon),
        new SFAInputMove(13, 14, alpha),
        new SFAInputMove(14, 14, alpha),
        new SFAInputMove(14, 15, space),
        new SFAInputMove(15, 16, big_C),
        new SFAInputMove(16, 17, colon),
        new SFAInputMove(17, 18, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(18, 19, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(19, 20, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(20, 21, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(21, 22, space),
        new SFAInputMove(22, 23, big_L),
        new SFAInputMove(23, 24, colon),
        new SFAInputMove(24, 25, alpha_num),
        new SFAInputMove(25, 26, space),
        new SFAInputMove(26, 27, big_D),
        new SFAInputMove(27, 28, colon),
        new SFAInputMove(28, 29, alpha),
        new SFAInputMove(29, 29, alpha),
        new SFAInputMove(29, 15, space)

      )



      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(29)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    prC4
  }

  def getProductParserCL4 : ParametricAutomaton = {
    val prCL4 = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, big_C),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(6, 7, space),
        new SFAInputMove(7, 8, big_L),
        new SFAInputMove(8, 9, colon),
        new SFAInputMove(9, 10, pt.MkAnd(alpha_num, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(10, 11, space),
        new SFAInputMove(11, 12, big_D),
        new SFAInputMove(12, 13, colon),
        new SFAInputMove(13, 14, alpha),
        new SFAInputMove(14, 14, alpha),
        new SFAInputMove(14, 15, space),
        new SFAInputMove(15, 16, big_C),
        new SFAInputMove(16, 17, colon),
        new SFAInputMove(17, 18, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(18, 19, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(19, 20, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(20, 21, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(21, 22, space),
        new SFAInputMove(22, 23, big_L),
        new SFAInputMove(23, 24, colon),
        new SFAInputMove(24, 25, pt.MkAnd(alpha_num, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(25, 26, space),
        new SFAInputMove(26, 27, big_D),
        new SFAInputMove(27, 28, colon),
        new SFAInputMove(28, 29, alpha),
        new SFAInputMove(29, 29, alpha),
        new SFAInputMove(29, 15, space)

      )



      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(29)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    prCL4
  }

  def getProductParserC6 : ParametricAutomaton = {
    val prC6 = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, big_C),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(6, 7, pt.MkAnd(not_space, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(7, 8, pt.MkAnd(not_space, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(8, 9, space),
        new SFAInputMove(9, 10, big_L),
        new SFAInputMove(10, 11, colon),
        new SFAInputMove(11, 12, alpha_num),
        new SFAInputMove(12, 13, space),
        new SFAInputMove(13, 14, big_D),
        new SFAInputMove(14, 15, colon),
        new SFAInputMove(15, 16, alpha),
        new SFAInputMove(16, 16, alpha),
        new SFAInputMove(16, 17, space),
        new SFAInputMove(17, 18, big_C),
        new SFAInputMove(18, 19, colon),
        new SFAInputMove(19, 20, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(20, 21, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(21, 22, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(22, 23, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(23, 24, pt.MkAnd(not_space, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(24, 25, pt.MkAnd(not_space, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(25, 26, space),
        new SFAInputMove(26, 27, big_L),
        new SFAInputMove(27, 28, colon),
        new SFAInputMove(28, 29, alpha_num),
        new SFAInputMove(29, 30, space),
        new SFAInputMove(30, 31, big_D),
        new SFAInputMove(31, 32, colon),
        new SFAInputMove(32, 33, alpha),
        new SFAInputMove(33, 33, alpha),
        new SFAInputMove(33, 17, space)

      )



      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(33)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    prC6
  }

  def getProductParserCL6 : ParametricAutomaton = {
    val prCL6 = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, big_C),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(6, 7, pt.MkAnd(not_space, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(7, 8, pt.MkAnd(not_space, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(8, 9, space),
        new SFAInputMove(9, 10, big_L),
        new SFAInputMove(10, 11, colon),
        new SFAInputMove(11, 12, pt.MkAnd(alpha_num, pt.FromFormula(c === i(p6)))),
        new SFAInputMove(12, 13, space),
        new SFAInputMove(13, 14, big_D),
        new SFAInputMove(14, 15, colon),
        new SFAInputMove(15, 16, alpha),
        new SFAInputMove(16, 16, alpha),
        new SFAInputMove(16, 17, space),
        new SFAInputMove(17, 18, big_C),
        new SFAInputMove(18, 19, colon),
        new SFAInputMove(19, 20, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(20, 21, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(21, 22, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(22, 23, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(23, 24, pt.MkAnd(not_space, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(24, 25, pt.MkAnd(not_space, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(25, 26, space),
        new SFAInputMove(26, 27, big_L),
        new SFAInputMove(27, 28, colon),
        new SFAInputMove(28, 29, pt.MkAnd(alpha_num, pt.FromFormula(c === i(p6)))),
        new SFAInputMove(29, 30, space),
        new SFAInputMove(30, 31, big_D),
        new SFAInputMove(31, 32, colon),
        new SFAInputMove(32, 33, alpha),
        new SFAInputMove(33, 33, alpha),
        new SFAInputMove(33, 17, space)

      )



      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(33)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    prCL6
  }

  def getProductParserCL9 : ParametricAutomaton = {
    val prC9 = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, big_C),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(6, 7, pt.MkAnd(not_space, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(7, 8, pt.MkAnd(not_space, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(8, 9, pt.MkAnd(not_space, pt.FromFormula(c === i(p6)))),
        new SFAInputMove(9, 10, pt.MkAnd(not_space, pt.FromFormula(c === i(p7)))),
        new SFAInputMove(10, 11, pt.MkAnd(not_space, pt.FromFormula(c === i(p8)))),
        new SFAInputMove(11, 12, space),
        new SFAInputMove(12, 13, big_L),
        new SFAInputMove(13, 14, colon),
        new SFAInputMove(14, 15, pt.MkAnd(alpha_num, pt.FromFormula(c === i(p9)))),
        new SFAInputMove(15, 16, space),
        new SFAInputMove(16, 17, big_D),
        new SFAInputMove(17, 18, colon),
        new SFAInputMove(18, 19, alpha),
        new SFAInputMove(19, 19, alpha),
        new SFAInputMove(19, 20, space),
        new SFAInputMove(20, 21, big_C),
        new SFAInputMove(21, 22, colon),
        new SFAInputMove(22, 23, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(23, 24, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(24, 25, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(25, 26, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(26, 27, pt.MkAnd(not_space, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(27, 28, pt.MkAnd(not_space, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(28, 29, pt.MkAnd(not_space, pt.FromFormula(c === i(p6)))),
        new SFAInputMove(29, 30, pt.MkAnd(not_space, pt.FromFormula(c === i(p7)))),
        new SFAInputMove(30, 31, pt.MkAnd(not_space, pt.FromFormula(c === i(p8)))),
        new SFAInputMove(31, 32, space),
        new SFAInputMove(32, 33, big_L),
        new SFAInputMove(33, 34, colon),
        new SFAInputMove(34, 35, pt.MkAnd(alpha_num, pt.FromFormula(c === i(p9)))),
        new SFAInputMove(35, 36, space),
        new SFAInputMove(36, 37, big_D),
        new SFAInputMove(37, 38, colon),
        new SFAInputMove(38, 39, alpha),
        new SFAInputMove(39, 39, alpha),
        new SFAInputMove(39, 20, space)

      )

      println("trans" + transitions)

      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(39)).asJava, pt)
      println("aut " + aut)
      new ParametricAutomaton(aut, pt)
    }
    prC9
  }

  def getProductParserC9 : ParametricAutomaton = {
    val prCL9 = {
      val transitions : Seq[pt.SFAMove] = List(

        new SFAInputMove(0, 1, big_C),
        new SFAInputMove(1, 2, colon),
        new SFAInputMove(2, 3, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(3, 4, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(4, 5, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(5, 6, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(6, 7, pt.MkAnd(not_space, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(7, 8, pt.MkAnd(not_space, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(8, 9, pt.MkAnd(not_space, pt.FromFormula(c === i(p6)))),
        new SFAInputMove(9, 10, pt.MkAnd(not_space, pt.FromFormula(c === i(p7)))),
        new SFAInputMove(10, 11, pt.MkAnd(not_space, pt.FromFormula(c === i(p8)))),
        new SFAInputMove(11, 12, space),
        new SFAInputMove(12, 13, big_L),
        new SFAInputMove(13, 14, colon),
        new SFAInputMove(14, 15, alpha_num),
        new SFAInputMove(15, 16, space),
        new SFAInputMove(16, 17, big_D),
        new SFAInputMove(17, 18, colon),
        new SFAInputMove(18, 19, alpha),
        new SFAInputMove(19, 19, alpha),
        new SFAInputMove(19, 20, space),
        new SFAInputMove(20, 21, big_C),
        new SFAInputMove(21, 22, colon),
        new SFAInputMove(22, 23, pt.MkAnd(not_space, pt.FromFormula(c === i(p0)))),
        new SFAInputMove(23, 24, pt.MkAnd(not_space, pt.FromFormula(c === i(p1)))),
        new SFAInputMove(24, 25, pt.MkAnd(not_space, pt.FromFormula(c === i(p2)))),
        new SFAInputMove(25, 26, pt.MkAnd(not_space, pt.FromFormula(c === i(p3)))),
        new SFAInputMove(26, 27, pt.MkAnd(not_space, pt.FromFormula(c === i(p4)))),
        new SFAInputMove(27, 28, pt.MkAnd(not_space, pt.FromFormula(c === i(p5)))),
        new SFAInputMove(28, 29, pt.MkAnd(not_space, pt.FromFormula(c === i(p6)))),
        new SFAInputMove(29, 30, pt.MkAnd(not_space, pt.FromFormula(c === i(p7)))),
        new SFAInputMove(30, 31, pt.MkAnd(not_space, pt.FromFormula(c === i(p8)))),
        new SFAInputMove(31, 32, space),
        new SFAInputMove(32, 33, big_L),
        new SFAInputMove(33, 34, colon),
        new SFAInputMove(34, 35, alpha_num),
        new SFAInputMove(35, 36, space),
        new SFAInputMove(36, 37, big_D),
        new SFAInputMove(37, 38, colon),
        new SFAInputMove(38, 39, alpha),
        new SFAInputMove(39, 39, alpha),
        new SFAInputMove(39, 20, space)

      )



      val aut = SFA.MkSFA(transitions.asJava, 0, List(new Integer(39)).asJava, pt)
      new ParametricAutomaton(aut, pt)
    }
    prCL9
  }

  val aut1 = getProductParserC2
  println("ip6 packet parser : \n" + aut1)
  val aut2 = getProductParserCL2
  println("aut 2 packet parser : \n" + aut2)
  val test2 = !aut2
  println("test complement: " + test2)

  //val test = reverseAut(aut2)
  //println("test reverse " + test)

  val test3 = test2 & aut1
  println("test 3 " + test3)

  val autId1 = seqTheory.autDatabase.registerAut(aut1)
  val autId2 = seqTheory.autDatabase.registerAut(test2)




  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(seqTheory)

    import seqTheory.{SeqSort, seq_in_re_id, seq_++, seq_empty, seq_reverse}

    var s1 = createConstant("s1", SeqSort)
    // membership in parameterised automaton
    !! (seq_in_re_id(s1, autId1))
    !! (seq_in_re_id(s1, autId2))
    //!! (seq_in_re_id(s1, autP3Id))
    // val l = (seq_++(s2,s3))
    //!! (l === s1)

    // global constraint on the parameters
    //!! (seqTheory.parameterTerms(0) >= 0)
    println(" res " + ???)
  }

}
