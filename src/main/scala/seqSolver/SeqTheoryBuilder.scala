
package seqSolver

import ap.theories.TheoryBuilder
import ap.theories.sequences.{SeqTheoryBuilder => MSeqTheoryBuilder}
import ap.types.Sort

class SeqTheoryBuilder extends MSeqTheoryBuilder {

  import TheoryBuilder.TheoryBuilderException

  val name = "Seq"

  private var elementSort : Sort = Sort.Integer

  def setElementSort(sort : Sort) : Unit =
    elementSort = sort

  lazy val theory = new SeqTheory(elementSort, List())

}
