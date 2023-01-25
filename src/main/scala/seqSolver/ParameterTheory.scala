
package seqSolver

import theory.{BooleanAlgebra, BooleanAlgebraSubst}
import utilities.Pair
import automata.sfa.{SFAMove => ASFAMove}
import transducers.sft.{SFTMove => ASFTMove}
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.theories.Theory
import ap.parser.{ConstantSubstVisitor, IConstant, IFormula, IFunction, ITerm}
import ap.types.Sort
import ap.terfor.{ConstantTerm, Term}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.substitutions.ConstantSubst
import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashSet, BitSet => MBitSet, HashMap => MHashMap, HashSet => MHashSet}


import java.util.Collection
import scala.collection.JavaConverters._

object ParameterTheory {

  def apply(charSort       : Sort,
            parameterSorts : Seq[Sort]   = Seq(),
            theories       : Seq[Theory] = Seq()) = {
    val charSymbols =
      Vector(charSort newConstant "l", charSort newConstant "l2")
    val parameters =
      (for ((s, n) <- parameterSorts.zipWithIndex)
       yield (s newConstant ("p" + n))).toIndexedSeq
    new ParameterTheory(charSymbols, parameters, theories)
  }

}

class ParameterTheory(val charSymbols : IndexedSeq[ConstantTerm],
                      val parameters  : IndexedSeq[ConstantTerm],
                      val theories    : Seq[Theory])
      extends BooleanAlgebraSubst[Conjunction, ITerm, ITerm] {

  type Pred          = Conjunction
  type Domain        = ITerm
  type SFAMove       = ASFAMove[Pred, Domain]
  type SFTMove       = ASFTMove[Pred, ITerm, Domain]

  val charSymbol     = charSymbols.head
  val charSort       = Sort sortOf charSymbol

  val parameterSorts = parameters map (Sort sortOf _)

  private val prover = SimpleAPI(enableAssert =SeqTheoryPlugin.enableAssertions)

  prover addTheories theories
  prover addConstantsRaw charSymbols
  prover addConstantsRaw parameters

  implicit val order = prover.order

  private val iCharSymbol0 = IConstant(charSymbol)
  private val iCharSymbol1 = IConstant(charSymbols(1))

  def False() = Conjunction.FALSE
  def True()  = Conjunction.TRUE

  def MkAtom(x: ITerm): Conjunction = // TODO: optimise
    prover.asConjunction(x === iCharSymbol0)

  def FromFormula(f : IFormula) : Conjunction = {
    prover.asConjunction(f)
  }
  def makeExistentialFormula(t : ITerm): Unit = {
    prover.makeExistential(t)
  }

  // TODO: reduce?

  def MkAnd(x: Conjunction, y: Conjunction): Conjunction =
    x & y

  def MkOr(x: Conjunction, y: Conjunction): Conjunction =
    x | y

  def MkNot(x: Conjunction): Conjunction =
    !x

  def MkAnd(x: Collection[Conjunction]): Conjunction =
    Conjunction.conj(x.asScala, order)

  def MkOr(x: Collection[Conjunction]): Conjunction =
    Conjunction.disj(x.asScala, order)

  def IsSatisfiable(x: Conjunction): Boolean = prover.scope {
    prover addAssertion x
    prover.??? == ProverStatus.Sat
  }

  def AreEquivalent(x: Conjunction, y: Conjunction): Boolean = prover.scope {
    // TODO: this won't work properly if x, y contain function symbols
    prover addConclusion (x <=> y)
    prover.??? == ProverStatus.Valid
  }

  def HasModel(x: Conjunction, y: ITerm): Boolean = prover.scope {
    prover addAssertion (iCharSymbol0 === y)
    prover addAssertion x
    prover.??? == ProverStatus.Sat
  }

  def HasModel(x: Conjunction, y: ITerm, z: ITerm): Boolean = prover.scope {
    prover addAssertion (iCharSymbol0 === y)
    prover addAssertion (iCharSymbol1 === z)
    prover addAssertion x
    prover.??? == ProverStatus.Sat
  }

  def generateWitness(x: Conjunction): ITerm = prover.scope {
    prover addAssertion x
    assert(prover.??? == ProverStatus.Sat)
    prover.evalToTerm(charSymbol)
  }

  def generateWitnesses(x: Conjunction): Pair[ITerm, ITerm] = prover.scope {
    prover addAssertion x
    assert(prover.??? == ProverStatus.Sat)
    prover.withCompleteModel { e =>
      new Pair(e(iCharSymbol0), e(iCharSymbol1))
    }
  }

  /**
   * Replaces every variable x in the unary function <code>f1</code>
   * the application to the function <code>f2</code> (f2(x))
   *
   * @return f1(f2(x))
   */
  override def MkSubstFuncFunc(f1: ITerm, f2: ITerm): ITerm = {
    val l = new MHashMap[ConstantTerm, ITerm]
    l.put(charSymbol, f1)
    ConstantSubstVisitor(f2, l)
  }

  /**
   * Replaces every variable x in the unary function <code>f</code>
   * with the constant <code>c</code>
   *
   * @return f(c)
   */
  override def MkSubstFuncConst(f: ITerm, s: Domain): Domain =  {
    val l = new MHashMap[ConstantTerm, ITerm]
    l.put(charSymbol, s)
    ConstantSubstVisitor(f, l)
  }
  /**
   * Replaces every variable x in the predicate <code>p</code>
   * with the application to the function <code>f</code> (f(x))
   *
   * @return p(f(x))
   */
  override def MkSubstFuncPred(f: ITerm, p: Pred): Pred = prover.scope {
    val l = new MHashMap[ConstantTerm, ITerm]
    l.put(charSymbol, f)
    prover.asConjunction(ConstantSubstVisitor(prover.asIFormula(p), l))
  }
  /**
   * Make a constant function initialized by the constant <code>s</code>
   *
   * @return lambda x.s
   */
  override def MkFuncConst(s: Domain): ITerm =  {
    s match {
      case IConstant(c) => c
      case _ => throw new Exception("MkFuncConst called with non constant")
    }
  }
  /**
   * Check whether <code>f1</code> and <code>f2</code> are equivalent relative to the predicate <code>p</code>
   *
   * @return lambda x.(p(x) and f1(x) != f2(x))
   */
  override def CheckGuardedEquality(p: Pred, f: ITerm, f1: ITerm): Boolean = prover.scope {
    ???
  }
  /**
   * get the restricted output based on <code>p</code> and <code>f</code>
   *
   * @return \psi(y) = \exists x. \phi(x) \wedge f(x)=y
   */
  override def getRestrictedOutput(p: Pred, f: ITerm): Pred = prover.scope {
    ???
  }
}
