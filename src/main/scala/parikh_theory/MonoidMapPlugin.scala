package uuverifiers.parikh_theory
import ap.proof.theoryPlugins.Plugin
import ap.terfor.preds.Atom
import ap.terfor.Term
import ap.proof.goal.Goal
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TerForConvenience._
import scala.collection.mutable.ArrayBuffer
import scala.collection.SortedSet
import ap.terfor.conjunctions.Conjunction
import collection.mutable.HashMap
import AutomataTypes._

/**
 * A theory plugin that will handle the connectedness of a given automaton,
 * associated with a given predicate, eliminating that predicate upon
 * subsumption.
 */
class MonoidMapPlugin(private val theoryInstance: ParikhTheory)
    extends Plugin
    with PredicateHandlingProcedure
    with NoAxiomGeneration
    with Tracing {

  private val transitionExtractor = new TransitionMaskExtractor(
    theoryInstance.transitionMaskPredicate
  )

  import transitionExtractor.{
    transitionStatusFromTerm,
    termMeansDefinitelyAbsent,
    goalAssociatedPredicateInstances,
    automataNr,
    transitionNr,
    transitionTerm,
    connectedAutId
  }

  // A cache for materialised automata. The first ones are the same as auts.
  private val materialisedAutomata =
    ArrayBuffer[Automaton](theoryInstance.auts: _*)

  override val procedurePredicate = theoryInstance.monoidMapPredicate

  private val stats = new Statistics()

  /**
   *  This callback is the entrypoint of the connectedness enforcement. It will
   *  determine subsumption, i.e. if there are no unknown transitions left on
   *  the last level of the prdouct. Upon subsumption it will remove the
   *  connectedness predicate and all associated helper predicates.
   *
   *  If we are not subsumed, we will continue with propagation or splitting.
   */
  override def handlePredicateInstance(
      goal: Goal
  )(predicateAtom: Atom): Seq[Plugin.Action] =
    trace("MonoidMapPlugin") {
      val context = Context(goal, predicateAtom)
      stats.increment("handlePredicateInstance")

      // FIXME!!!
      val materialiseActions =
        if (context.activeAutomata.size > 1)
          handleMaterialise(context)
        else Seq()

      handleMonoidMapSubsumption(context) ++ context.connectedInstances.flatMap(
        handleConnectedInstance(_, context)
      ) ++ materialiseActions ++ handleSplitting(context)
    }

  private def handleMonoidMapSubsumption(context: Context) =
    trace("handleMonoidMapSubsumption") {
      import context.{
        activeAutomata,
        connectedInstances,
        monoidMapPredicateAtom,
        transitionMasks
      }

      val productIsDone =
        trace("productIsDone")(activeAutomata.size <= 1)
      val allAutomataGuaranteedConnected = connectedInstances.isEmpty
      val isSubsumed =
        trace("isSubsumed")(productIsDone && allAutomataGuaranteedConnected)

      if (isSubsumed) {
        val removeAssociatedPredicates =
          transitionMasks.map(Plugin.RemoveFacts(_))
        val removeThisPredicateInstance =
          Plugin.RemoveFacts(monoidMapPredicateAtom)

        stats.report()

        removeAssociatedPredicates :+ removeThisPredicateInstance
      } else {
        Seq()
      }
    }

  private def handleSplitting(context: Context) = trace("handleSplitting") {
    stats.increment("handleSplitting")
    val splitter = new TransitionSplitter()

    goalState(context.goal) match {
      case Plugin.GoalState.Final => splitter.handleGoal(context.goal)
      case _                      => List(Plugin.ScheduleTask(splitter, 0))
    }
  }

  private def handleMaterialise(context: Context) = trace("handleMaterialise") {
    val knownConnectedAutomataNrs: Seq[Int] =
      trace("knownConnectedAutomataNrs")(
        context.activeAutomata
          .diff(context.automataWithConnectedPredicate)
          .toSeq
      )

    // TODO better heuristic for >2!
    // TODO should we start materialise single automata?
    knownConnectedAutomataNrs match {
      case Seq()  => Seq()
      case Seq(_) => Seq()
      case Seq(left, right) =>
        materialiseProduct(left, right, context)
      case fst +: snd +: _ =>
        materialiseProduct(fst, snd, context)
    }
  }

  // TODO make this a PredicateHandlingProcedure?
  private def handleConnectedInstance(
      connectedInstance: Atom,
      context: Context
  ) = trace(s"handleConnectedInstance ${connectedInstance}") {

    val autId = connectedAutId(connectedInstance)
    val myTransitionMasks = context.autTransitionMasks(autId)
    val aut = materialisedAutomata(autId)
    val transitionToTerm = context.autTransitionTerm(autId)(_)

    implicit val order = context.goal.order

    // TODO compute a cut to find which dead transitions contribute to the conflict!

    val deadTransitions = trace("deadTransitions") {
      aut.transitions
        .filter(
          t => termMeansDefinitelyAbsent(context.goal, transitionToTerm(t))
        )
        .toSet
    }

    val filteredGraph = aut.dropEdges(deadTransitions)

    val knownUnreachableStates = trace("knownUnreachableStates") {
      filteredGraph.unreachableFrom(aut.initialState)
    }

    // val possiblyUnreachableEdges = trace("possiblyUnreachableEdges") {
    //   filteredGraph
    //     .unreachableFrom(
    //       aut.initialState,
    //       t => termMeansPossiblyAbsent(context.goal, transitionToTerm(t))
    //     )
    //     .flatMap(filteredGraph.transitionsFrom(_))
    // }
    // FIXME why doesn't this work for subsumption? possiblyUnreachableEdges

    val unknownEdges = trace("unknownEdges")(
      context.autTransitionTermsUnordered(autId) filter (
          t => transitionStatusFromTerm(context.goal, t).isUnknown
      )
    )

    val allTransitionsAssigned = unknownEdges.isEmpty || context
      .autTransitionTermsUnordered(autId)
      .isEmpty

    val subsumeActions =
      if (allTransitionsAssigned) Seq(Plugin.RemoveFacts(connectedInstance))
      else Seq()

    // constrain any terms associated with a transition from a
    // *known* unreachable state to be = 0 ("not used").
    val unreachableActions = trace("unreachableActions") {
      val unreachableConstraints =
        conj(
          knownUnreachableStates
            .flatMap(
              aut.transitionsFrom(_).map(transitionToTerm(_) === 0)
            )
        )

      if (unreachableConstraints.isTrue) Seq() // TODO why not subsume?
      else
        Seq(
          Plugin.AddAxiom(
            myTransitionMasks :+ connectedInstance, // FIXME limit to deadTransitions transitionMask:s
            unreachableConstraints,
            theoryInstance
          )
        )
    }

    unreachableActions ++ subsumeActions

  }

  private def materialiseProduct(
      leftId: Int,
      rightId: Int,
      context: Context
  ) = {
    stats.increment("materialiseProduct")

    val left = context.filteredAutomaton(leftId)
    val right = context.filteredAutomaton(rightId)
    trace(
      s"materialising product of ${left.transitions.toSeq} and ${right.transitions.toSeq}"
    )("")

    val annotatedProduct = left.productWithSources(right)
    val product = annotatedProduct.product

    val newAutomataNr = trace("newAutomataNr")(materialisedAutomata.size)
    materialisedAutomata += product

    val removeTransitionMasks =
      context.transitionMasks.map(Plugin.RemoveFacts(_))
    val removeConnectedPredicates = context.connectedInstances
      .filter(m => automataNr(m) == leftId || automataNr(m) == rightId)
      .map(Plugin.RemoveFacts(_))

    // TODO figure out how to generate a nice blocking clause
    val productClauses = if (product.isEmpty()) {
      Seq(
        Plugin.AddAxiom(
          context.autTransitionMasks(leftId) ++ context.autTransitionMasks(
            rightId
          ) :+ context.monoidMapPredicateAtom,
          Conjunction.FALSE,
          theoryInstance
        )
      )
    } else {
      formulaForNewAutomaton(
        newAutomataNr,
        leftId,
        rightId,
        annotatedProduct,
        context
      )

    }

    removeTransitionMasks ++ removeConnectedPredicates ++ productClauses
  }

  private def formulaForNewAutomaton(
      productNr: Int,
      leftNr: Int,
      rightNr: Int,
      annotatedProduct: AnnotatedProduct,
      context: Context
  ) = {
    import ap.basetypes.IdealInt.ZERO

    implicit val order = context.goal.order
    val varFactory = new FreshVariables(0)
    val transitionToTerm = trace("product transitionToTerm")(
      materialisedAutomata(productNr).transitions
        .map(t => (t, varFactory.nextVariable()))
        .toMap
    )

    val newClauses = theoryInstance.automataClauses(
      materialisedAutomata(productNr),
      context.instanceTerm,
      productNr,
      transitionToTerm.toIndexedSeq
    )

    // - x(t) = sum(e : termProductEdges(t, default=0))
    val bridgingClauses = trace("Bridging clauses") {
      val productTransitionToLc = transitionToTerm.andThen(l(_)(order))

      Seq(leftNr, rightNr).flatMap(
        autNr => {
          val transitionToTerm = context.autTransitionTerm(autNr)(_)
          val originTerm =
            if (autNr == leftNr) TermOrigin.Left else TermOrigin.Right
          val productTermsFrom = annotatedProduct.resultsOf(originTerm)(_)

          materialisedAutomata(autNr).transitions.map(
            termTransition =>
              trace(s"a${autNr} bridge: ${termTransition}")(
                transitionToTerm(termTransition) === productTermsFrom(
                  termTransition
                ).map(
                    productEdges =>
                      lcSum(productEdges.map(productTransitionToLc))
                  )
                  .getOrElse(
                    trace(
                      s"a${autNr}::${termTransition} not in product ${productNr}"
                    )(l(ZERO))
                  )
              )
          )
        }
      )

    }

    // FIXME maybe simplify?

    Seq(
      Plugin.AddAxiom(
        context.autTransitionMasks(leftNr) ++ context.autTransitionMasks(
          rightNr
        ) :+ context.monoidMapPredicateAtom,
        varFactory.exists(conj(newClauses ++ bridgingClauses)),
        theoryInstance
      )
    )

  }

  /**
   * This class captures common contextual values that can be extracted from a
   * proof goal.
   */
  sealed case class Context(val goal: Goal, val monoidMapPredicateAtom: Atom) {
    val instanceTerm = monoidMapPredicateAtom(0)
    implicit val order = goal.order

    private val transitionTermCache = HashMap[Int, Map[Transition, Term]]()

    lazy val connectedInstances = trace("connectedInstances")(
      goalAssociatedPredicateInstances(
        goal,
        instanceTerm,
        theoryInstance.connectedPredicate
      )
    )

    lazy val automataWithConnectedPredicate = SortedSet(
      connectedInstances.map(connectedAutId): _*
    )

    lazy val transitionMasks = trace("transitionMasks")(
      goalAssociatedPredicateInstances(
        goal,
        instanceTerm,
        theoryInstance.transitionMaskPredicate
      )
    )

    lazy val activeAutomata = trace("activeAutomata") {
      SortedSet(
        transitionMasks
          .map(automataNr): _*
      )
    }

    // FIXME memoise
    def transitionStatus(autId: Int)(transition: Transition) =
      transitionStatusFromTerm(goal, l(autTransitionTerm(autId)(transition)))

    private def getOrUpdateTransitionTermMap(autId: Int) = {
      val autMap: Map[Transition, Term] =
        transitionTermCache.getOrElseUpdate(
          autId,
          trace(s"getOrUpdateTransitionTermMap::compute(${autId})")(
            materialisedAutomata(autId).transitions
              .zip(autTransitionMasks(autId).map(transitionTerm).iterator)
              .toMap
          )
        )
      autMap
    }

    def autTransitionTerm(autId: Int)(transition: Transition): Term =
      getOrUpdateTransitionTermMap(autId)(transition)

    def autTransitionTermsUnordered(autId: Int) =
      getOrUpdateTransitionTermMap(autId).values

    // FIXME memoise
    def autTransitionMasks(autId: Int) =
      transitionMasks
        .filter(automataNr(_) == autId)
        .sortBy(transitionNr)
        .toIndexedSeq

    // FIXME excellent candidate for memoisation!
    def filteredAutomaton(autId: Int) =
      materialisedAutomata(autId).filterTransitions(
        t =>
          !termMeansDefinitelyAbsent(
            goal,
            l(autTransitionTerm(autId)(t))(goal.order)
          )
      )

    val monoidValues = monoidMapPredicateAtom.tail
  }

  class TransitionSplitter() extends PredicateHandlingProcedure with Tracing {

    private val transitionPredicate = theoryInstance.transitionMaskPredicate
    override val procedurePredicate = transitionPredicate

    override def handlePredicateInstance(
        goal: Goal
    )(predicateAtom: Atom): Seq[Plugin.Action] = trace("TransitionSplitter") {

      val context = Context(goal, predicateAtom)
      implicit val order = goal.order

      val unknownTransitions = trace("unknownTransitions") {
        context.automataWithConnectedPredicate.unsorted
          .flatMap { aNr =>
            val automaton = materialisedAutomata(aNr)
            automaton
              .startBFSFrom(automaton.initialState)
              .flatMap(automaton.transitionsFrom)
              .filter(
                context.transitionStatus(aNr)(_).isUnknown
              )
              .map(context.autTransitionTerm(aNr))

          }

      }

      trace("unknownActions") {
        def transitionToSplit(transitionTerm: LinearCombination) =
          Plugin.AxiomSplit(
            Seq(),
            Seq(transitionTerm <= 0, transitionTerm > 0)
              .map(eq => (conj(eq), Seq())),
            theoryInstance
          )

        val splittingActions = trace("splittingActions") {
          unknownTransitions
            .map(transitionToSplit(_))
        }

        if (splittingActions.isEmpty) Seq() else Seq(splittingActions.head)

      }
    }
  }

  def dumpGraphs() = {
    materialisedAutomata.zipWithIndex.foreach {
      case (a, i) =>
        // TODO extract transition labels and annotate the graph with them
        a.dumpDotFile(
          s"monoidMapTheory-${this.theoryInstance.hashCode()}-aut-${i}.dot"
        )
    }
  }

}
