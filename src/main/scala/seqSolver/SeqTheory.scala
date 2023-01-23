

package seqSolver

import seqSolver.automataIntern.AutDatabase
import ap.Signature
import ap.basetypes.IdealInt
import ap.parser.IExpression.Predicate
import ap.parser._
import ap.theories.{Theory, TheoryRegistry}
import ap.theories.sequences.{SeqTheory => MSeqTheory}
import ap.types.{MonoSortedIFunction, MonoSortedPredicate, ProxySort, Sort}
import ap.terfor.conjunctions.Conjunction

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashMap => MHashMap, Map => MMap,
                                 Set => MSet, ArrayBuffer}

object SeqTheory {

}


class SeqTheory(elementSort : Sort,
                parameters  : Seq[(String, Sort)]) extends MSeqTheory {

  val ElementSort = elementSort

  object SeqSort extends ProxySort(Sort.Integer) {
    import IExpression._

    override val name = "Seq[" + elementSort + "]"

    override def individuals : Stream[ITerm] = elementLists

    private lazy val elementLists : Stream[ITerm] =
      seq_empty() #::
      (for (tail <- elementLists; t <- ElementSort.individuals)
       yield seq_cons(t, tail))

    override def decodeToTerm(
                   d : IdealInt,
                   assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      assignment get (d, this)

    override def augmentModelTermSet(
                            model : Conjunction,
                            terms : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = {
      val emptyAtoms = model.predConj.positiveLitsWithPred(_seq_empty)
      val consAtoms  = model.predConj.positiveLitsWithPred(_seq_cons)

      for (a <- emptyAtoms)
        terms.put((a.last.constant, this), seq_empty())

      var oldSize = -1
      while (terms.size > oldSize) {
        oldSize = terms.size

        for (a <- consAtoms) {
          definedTerms += ((a.last.constant, this))

          for (head <- ElementSort.decodeToTerm(a(0).constant, terms);
               tail <- terms.get((a(1).constant, this)))
            terms.put((a(2).constant, this), seq_cons(head, tail))
        }
      }
    }
  }

  private val prefix = SeqSort.name + "_"

  private val ESo = elementSort
  private val SSo = SeqSort

  import Sort.{Nat, Integer}

  val seq_empty =
    new MonoSortedIFunction(prefix + "empty", List(), SSo, true, false)
  val seq_cons =
    new MonoSortedIFunction(prefix + "cons", List(ESo, SSo), SSo, true, false)
  val seq_unit =
    new MonoSortedIFunction("seq_unit", List(ESo), SSo, true, false)

  val seq_++ =
    new MonoSortedIFunction(prefix + "++", List(SSo, SSo), SSo, true, false)

  val seq_len =
    new MonoSortedIFunction("seq_len", List(SSo), Nat, true, false)
  val seq_extract =
    new MonoSortedIFunction("seq_extract", List(SSo, Nat, Nat), SSo, true,false)
  val seq_indexof =
    new MonoSortedIFunction("seq_indexof",
                            List(SSo, ESo, Integer), Integer, true, false)
  val seq_at =
    new MonoSortedIFunction("seq_at", List(SSo, Nat), SSo, true, false)
  val seq_nth =
    new MonoSortedIFunction("seq_nth", List(SSo, Nat), ESo, true, false)

  val seq_update =
    new MonoSortedIFunction("seq_update", List(SSo, Nat, SSo), SSo, true, false)

  val seq_contains =
    new MonoSortedPredicate("seq_contains", List(SSo, SSo))
  val seq_prefixof =
    new MonoSortedPredicate("seq_prefixof", List(SSo, SSo))
  val seq_suffixof =
    new MonoSortedPredicate("seq_suffixof", List(SSo, SSo))
  val seq_replace =
    new MonoSortedIFunction("seq_replace",
                            List(SSo, SSo, SSo), SSo, true, false)

  val seq_in_re_id =
    new MonoSortedPredicate(prefix + "in_re_id", List(SeqSort, Sort.Integer))

  val parameterFuns =
    (for ((name, sort) <- parameters)
     yield MonoSortedIFunction(name, List(), sort, true, false)).toIndexedSeq

  val parameterTerms =
    for (f <- parameterFuns) yield IFunApp(f, List())

  // A predicate to record that we generate a model for some term
  // ourselves
  val seqConstant = new Predicate(prefix + "constant", 1)

  val functions =
    List(seq_empty, seq_cons, seq_unit, seq_++,
         seq_len, seq_extract, seq_indexof, seq_at, seq_nth,
         seq_update, seq_replace) ++ parameterFuns
  val additionalPredicates =
    List(seq_in_re_id, seq_contains, seq_prefixof, seq_suffixof, seqConstant)

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

  val parameterPreds = for (f <- parameterFuns) yield functionPredicateMap(f)

  // TODO: add dependencies as derived from sorts

  override val modelGenPredicates = Set(seqConstant)

  def plugin = Some(new SeqTheoryPlugin(this))

  val _seq_empty = functionPredicateMap(seq_empty)
  val _seq_cons  = functionPredicateMap(seq_cons)

  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary  => true
      case Theory.SatSoundnessConfig.Existential => true
      case Theory.SatSoundnessConfig.General     => false
    }

  //////////////////////////////////////////////////////////////////////////////

  override def toString = sort.name

  private val predFunMap =
    (for ((f,p) <- functionPredicateMap) yield (p,f)).toMap

  object FunPred {
    def apply(f : IFunction) : Predicate = functionPredicateMap(f)
    def unapply(p : Predicate) : Option[IFunction] = predFunMap get p
  }

  TheoryRegistry register this
  MSeqTheory register this

}
