

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
import transducers.sft.{SFT, SFTInputMove, SFTMove}

import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}
import scala.collection.JavaConverters._

object SRATest extends App {

  import IExpression._

  val seqTheory = new SeqTheory(Sort.Integer,
    List(("p0", Sort.Integer), ("p1", Sort.Integer),("p2", Sort.Integer),("p3", Sort.Integer),("p4", Sort.Integer),("p5", Sort.Integer),("p6", Sort.Integer),("p7", Sort.Integer),("p8", Sort.Integer)))

  val pt = seqTheory.parameterTheory
  val Seq(p0, p1, p2, p3, p4, p5, p6, p7, p8)  = seqTheory.parameterTheoryPars
  val Seq(c, c1) = seqTheory.parameterTheoryChars
  val num = pt.FromFormula(i(48) <= c & c <= i(57))
  val dot = pt.FromFormula(i(46) === ConstantTerm2ITerm(c))
  val space = pt.FromFormula(i(32) === ConstantTerm2ITerm(c))
  val lower_alpha = pt.FromFormula(i(97) <= c & c <= i(122))
  val upper_alpha = pt.FromFormula(i(65) <= c & c <= i(90))
  val alpha_num = Conjunction.disj(Seq(num, lower_alpha, upper_alpha), pt.order)
  val backslash = pt.FromFormula(i(92) === ConstantTerm2ITerm(c))
  val colon = pt.FromFormula(i(58) === ConstantTerm2ITerm(c))
  val small_s = pt.FromFormula(i(115) === ConstantTerm2ITerm(c))
  val small_d = pt.FromFormula(i(100) === ConstantTerm2ITerm(c))
  val small_p = pt.FromFormula(i(112) === ConstantTerm2ITerm(c))

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


  val aut = getIP2PacketParser()
  println("ip2 packet parser : \n" + aut)

  val autId = seqTheory.autDatabase.registerAut(aut)




  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(seqTheory)

    import seqTheory.{SeqSort, seq_in_re_id, seq_++}

    var s1 = createConstant("s1", SeqSort)
    // membership in parameterised automaton
    !! (seq_in_re_id(s1, autId))
    //!! (seq_in_re_id(s1, autP3Id))
    // val l = (seq_++(s2,s3))
    //!! (l === s1)

    // global constraint on the parameters
    //!! (seqTheory.parameterTerms(0) >= 0)
    println(" res " + ???)
  }

}
