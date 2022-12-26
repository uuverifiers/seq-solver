

package seqSolver

import seqSolver.automataIntern.AutDatabase

import ap.Signature
import ap.parser._
import ap.theories.{Theory, TheoryRegistry}
import ap.types.{Sort, ProxySort, MonoSortedIFunction, MonoSortedPredicate}
import ap.terfor.conjunctions.Conjunction

object SeqTheory {

}


class SeqTheory(elementSort : Sort,
                parameters  : Seq[(String, Sort)]) extends Theory {

  object SeqSort extends ProxySort(Sort.Integer) {
    override val name = "Seq[" + elementSort + "]"
    
  }

  val sort = SeqSort

  private val prefix = SeqSort.name + "_"

  private val ESo = elementSort
  private val SSo = SeqSort

  val seq_empty =
    new MonoSortedIFunction(prefix + "empty", List(), SSo, true, false)
  val seq_cons =
    new MonoSortedIFunction(prefix + "cons", List(ESo, SSo), SSo, true, false)
  val seq_head =
    new MonoSortedIFunction(prefix + "head", List(SSo), ESo, true, false)
  val seq_tail =
    new MonoSortedIFunction(prefix + "tail", List(SSo), SSo, true, false)

  val seq_++ =
    new MonoSortedIFunction(prefix + "++", List(SSo, SSo), SSo, true, false)

  val seq_in_re_id =
    new MonoSortedPredicate(prefix + "in_re_id", List(SeqSort, Sort.Integer))

  val parameterFuns =
    (for ((name, sort) <- parameters)
     yield MonoSortedIFunction(name, List(), sort, true, false)).toIndexedSeq

  val parameterTerms =
    for (f <- parameterFuns) yield IFunApp(f, List())

  val functions =
    List(seq_empty, seq_cons, seq_head, seq_tail, seq_++) ++ parameterFuns
  val additionalPredicates =
    List(seq_in_re_id)

  //////////////////////////////////////////////////////////////////////////////

  val parameterTheoryChars =
    Vector(elementSort newConstant "c", elementSort newConstant "c1")
  val parameterTheoryPars =
    (for ((n, s) <- parameters) yield (s newConstant n)).toIndexedSeq

  val parameterTheory =
    new ParameterTheory(parameterTheoryChars, parameterTheoryPars, List())

  val autDatabase = new AutDatabase(this)

  //////////////////////////////////////////////////////////////////////////////

  val allAxioms = {
    import IExpression._

    and(for (((_, s), f) <- parameters zip parameterFuns)
        yield s.ex(x => f() === x))
  }

  //////////////////////////////////////////////////////////////////////////////

  val (predicates, axioms, _, functionPredicateMap) =
    Theory.genAxioms(theoryFunctions = functions,
                     extraPredicates = additionalPredicates,
                     theoryAxioms    = allAxioms)
  
  val functionPredicateMapping =
    for (f <- functions) yield (f, functionPredicateMap(f))
  val functionalPredicates =
    (for (f <- functions) yield functionPredicateMap(f)).toSet
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val totalityAxioms = Conjunction.TRUE
  val triggerRelevantFunctions : Set[IFunction] = Set()

  // TODO: add dependencies as derived from sorts

  def plugin = Some(new SeqTheoryPlugin(this))

  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary  => true
      case Theory.SatSoundnessConfig.Existential => true
      case Theory.SatSoundnessConfig.General     => false
    }

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString = sort.name

}
