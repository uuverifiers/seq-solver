
package seqSolver

import theory.BooleanAlgebra
import utilities.Pair
import automata.sfa.{SFAMove => ASFAMove}

import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.theories.Theory
import ap.parser.{ITerm, IConstant, IFormula}
import ap.types.Sort
import ap.terfor.{Term, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier}

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
      extends BooleanAlgebra[Conjunction, ITerm] {

  type Pred          = Conjunction
  type Domain        = ITerm
  type SFAMove       = ASFAMove[Pred, Domain]

  val charSymbol     = charSymbols.head
  val charSort       = Sort sortOf charSymbol

  val parameterSorts = parameters map (Sort sortOf _)

  private val prover = SimpleAPI.spawnWithAssertions

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

}
