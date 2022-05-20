import uuverifiers.common.{AutomatonBuilder, IntState, SymbolicTransition}

object AutomatonLibrary {
  import scala.language.implicitConversions
  implicit def int2State(idx: Int): IntState = IntState(idx)
  import uuverifiers.common.SymbolicLabelConversions.charToSymbolicLabel

  val automata = Map(
    "trivial" -> AutomatonBuilder()
      .addStates(IntState(0, 1))
      .setInitial(IntState(0))
      .setAccepting(IntState(1))
      .addTransition(new SymbolicTransition(IntState(0), 'a', IntState(1)))
      .getAutomaton(),
    "fourStatePerTransitionWithLoop" -> AutomatonBuilder()
      .addStates(IntState(0 to 3))
      .setAccepting(IntState(3))
      .setInitial(IntState(0))
      .addTransition(new SymbolicTransition(0, 'a', 1))
      .addTransition(new SymbolicTransition(0, '-', 2))
      .addTransition(new SymbolicTransition(1, '-', 3))
      .addTransition(new SymbolicTransition(1, 'b', 0))
      .addTransition(new SymbolicTransition(2, '-', 3))
      .addTransition(new SymbolicTransition(2, 'c', 2))
      .addTransition(new SymbolicTransition(3, '-', 2))
      .getAutomaton(),
    "threeStateLoopFree" -> AutomatonBuilder()
      .addStates(List(0, 1, 2))
      .setInitial(0)
      .setAccepting(1, 2)
      .addTransition(new SymbolicTransition(0, 'c', 2))
      .addTransition(new SymbolicTransition(0, 'a', 1))
      .addTransition(new SymbolicTransition(1, 'b', 2))
      .getAutomaton()
  )

  val trivial = automata("trivial")

  //              b
  //         +---------+
  //         v         |
  //       +---+  a  +---+  #2 +---+
  //   --> | 0 | --> | 1 | --> | 3 | -->
  //       +---+     +---+     +---+
  //         |                 | ^
  //         | #1       #5     | |
  //         v     +-----------+ |
  //       +---+<--+    #4       |
  //       | 2 | ----------------+
  //       +---+
  //       |   ^
  //       +---+
  //         c
  val fourStatePerTransitionWithLoop = automata(
    "fourStatePerTransitionWithLoop"
  )

  //              c
  //       +--------------------------------+
  //       |                                v
  //     +---+    a       #===#     b     #===#
  // --> | 0 | ---------> H 1 H --------> H 2 H
  //     +---+            #===#           #===#
  val threeStateLoopFree = automata("threeStateLoopFree")

  val allAutomata = automata.values
}
