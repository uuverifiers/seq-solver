

package seqSolver

import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin

class SeqTheoryPlugin(theory : SeqTheory) extends Plugin {

  override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
    goalState(goal) match {
      case Plugin.GoalState.Final => {
        println("have to solve: " + goal.facts)
        List()
      }
      case _ => {
        List()
      }
    }
  }

}
