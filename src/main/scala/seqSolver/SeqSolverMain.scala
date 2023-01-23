
package seqSolver

/**
 * Wrapper around <code>ap.CmdlMain</code>, adding the option
 * <code>-seqSolver=seqSolver.SeqTheory</code>.
 */
object SeqSolverMain {

  val version = "unstable build (Princess: " + ap.CmdlMain.version + ")"

  /**
   * The options forwarded to Princess. They will be overwritten by options
   * specified on the command line, so it is possible to provide more specific
   * string solver options on the command line.
   */
  val options = List("-seqSolver=seqSolver.SeqTheory", "-logo")

  def main(args: Array[String]) : Unit =
    ap.CmdlMain.main((options ++ args).toArray)

}
