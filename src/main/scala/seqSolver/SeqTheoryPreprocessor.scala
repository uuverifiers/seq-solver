
package seqSolver

import ap.basetypes.IdealInt
import ap.parser._

import seqSolver.automataIntern.AutDatabase

/**
 * Pre-processor for reducing some operators to more basic ones.
 */
class SeqTheoryPreprocessor(theory : SeqTheory)
      extends CollectingVisitor[Unit, IExpression] {

  import theory.{seq_cons, seq_++, seq_unit, seq_in_re_id,
                 SeqSort, ElementSort, autDatabase, allocateCharParameter}
  import IExpression._

  def apply(f : IFormula) : IFormula =
    this.visit(f, Context(())).asInstanceOf[IFormula]

  override def preVisit(t : IExpression,
                        ctxt : Unit) : PreVisitResult = t match {
    case IFunApp(`seq_cons`, Seq(head, tail)) =>
      TryAgain(seq_++(seq_unit(head), tail), ctxt)
    case _ =>
      KeepArg
  }

  def postVisit(t : IExpression,
                ctxt : Unit,
                subres : Seq[IExpression]) : IExpression = (t, subres) match {
    case (IFunApp(`seq_unit`, _), Seq(t@Const(_))) => {
      val id = autDatabase.registerRegex(AutDatabase.CharRegex(t))
      SeqSort.eps { res => seq_in_re_id(res, id) }
    }

    case (IFunApp(`seq_unit`, _), Seq(charTerm : ITerm)) => {
      val (p, t) = allocateCharParameter
      val id = autDatabase.registerRegex(AutDatabase.ParamMatchRegex(p))
      SeqSort.eps { res => seq_in_re_id(res, id) & (t === charTerm) }
    }

      // TODO: generalise to handle also seq.contains, seq.prefixof, seq.suffixof

    case _ =>
      t update subres

  }

}
