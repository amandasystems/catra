package uuverifiers.parikh_theory
import WhyCantIDefineGlobalTypeAliasesGoddammit.TransitionToCounterOffsets
import java.math.BigInteger

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

}
