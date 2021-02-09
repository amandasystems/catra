package uuverifiers.parikh_theory

// This describes the status of a transition in the current model
protected sealed trait TransitionSelected {
  def definitelyAbsent = false
  def isUnknown = false
}

object TransitionSelected {
  case object Present extends TransitionSelected
  case object Absent extends TransitionSelected {
    override def definitelyAbsent = true
  }
  case object Unknown extends TransitionSelected {
    override def isUnknown = true
  }
}
