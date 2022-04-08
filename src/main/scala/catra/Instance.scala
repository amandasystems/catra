package uuverifiers.catra
import WhyCantIDefineGlobalTypeAliasesGoddammit.TransitionToCounterOffsets
import java.math.BigInteger
import uuverifiers.common.Automaton

sealed case class Instance(
    counters: Seq[Counter],
    automata: Seq[Seq[Automaton]],
    // These are global because we ensure all automata have mutually independent state IDs!
    transitionToOffsets: TransitionToCounterOffsets,
    constraints: Seq[Formula]
) {

  private def canAcceptRegisterAssignment(a: Automaton): Boolean = ???

  def verifyCounterAssignment(
      counterValues: Map[Counter, BigInteger]
  ): Boolean = {
    automata.forall(group => group.forall(canAcceptRegisterAssignment)) && constraints
      .forall(
        _.accepts(counterValues)
      )
  }

  private def allAutomata() = automata.flatten.toSeq
  private def allTransitions() = allAutomata().flatMap(_.transitions)
  private def isLive(c: Counter) =
    allTransitions().exists(t => transitionToOffsets(t) contains c)

  /**
   The live counters are counters constrained by one or more transition of one
   or more automaton. Note that non-live counters can appear in constraints,
   where they can take any value. It is therefore not necessarily an error to
   include them, but it is a near-certain sign of a mistake in the input model
   and should trigger a warning.
  **/
  lazy val liveCounters = counters.filter(isLive(_))
}
