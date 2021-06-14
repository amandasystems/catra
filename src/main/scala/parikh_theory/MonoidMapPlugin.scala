package uuverifiers.parikh_theory
import ap.proof.theoryPlugins.Plugin
import ap.terfor.preds.Atom
import ap.proof.goal.Goal
import ap.parser.IExpression.Predicate
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TerForConvenience._
import ap.terfor.Formula
import scala.collection.mutable.ArrayBuffer

/**
 * A theory plugin that will handle the connectedness of a given automaton,
 * associated with a given predicate, eliminating that predicate upon
 * subsumption.
 */
class MonoidMapPlugin[A <: Automaton](
    private val theoryInstance: ParikhTheory[A]
) extends Plugin
    with PredicateHandlingProcedure
    with NoAxiomGeneration
    with Tracing {

  private val transitionExtractor = new TransitionMaskExtractor(
    theoryInstance.transitionMaskPredicate
  )

  import transitionExtractor.{
    transitionStatusFromTerm,
    termMeansDefinitelyAbsent,
    termMeansPossiblyAbsent,
    goalAssociatedPredicateInstances,
    automataNr,
    transitionNr,
    transitionTerm,
    connectedAutId
  }

  private val auts = theoryInstance.auts

  private val maxDepth = auts.size - 1

  // A cache for materialised automata. The first ones are the same as auts.
  private val materialisedAutomata = ArrayBuffer[A](theoryInstance.auts: _*)

  override val procedurePredicate = theoryInstance.monoidMapPredicate

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
      val instanceTerm = predicateAtom(0)

      val connectedInstances = trace("connectedInstances")(
        goalAssociatedPredicateInstances(
          goal,
          instanceTerm,
          theoryInstance.connectedPredicate
        )
      )

      val transitionMasks = trace("transitionMasks")(
        goalAssociatedPredicateInstances(
          goal,
          instanceTerm,
          theoryInstance.transitionMaskPredicate
        )
      )

      // FIXME: sort this for determinism
      val activeAutomata = trace("activeAutomata") {
        transitionMasks
          .map(automataNr)
          .toSet
      }

      val connectedActions = trace("connectedActions")(
        connectedInstances.flatMap(
          handleConnectedInstance(_, transitionMasks, goal)
        )
      )

      val materialiseActions = handleMaterialise(
        activeAutomata,
        connectedInstances,
        transitionMasks
      )

      // TODO this should be a separate fn
      val subsumedActions = trace("subsumedActions") {
        val productIsDone = trace("productIsDone")(activeAutomata.size == 1)
        val allAutomataGuaranteedConnected = connectedInstances.isEmpty
        val isSubsumed =
          trace("isSubsumed")(productIsDone && allAutomataGuaranteedConnected)

        if (isSubsumed) {
          val removeAssociatedPredicates =
            transitionMasks.map(Plugin.RemoveFacts(_))
          val removeThisPredicateInstance = Plugin.RemoveFacts(predicateAtom)
          removeAssociatedPredicates :+ removeThisPredicateInstance
        } else {
          Seq()
        }
      }

      subsumedActions ++ connectedActions ++ materialiseActions
    }

  private def handleMaterialise(
      activeAutomata: Set[Int],
      connectedInstances: IndexedSeq[Atom],
      transitionMasks: IndexedSeq[Atom]
  ) = trace("handleMaterialise") {

    // find all automata with transitionterms but whose number is not in the set
    // of connnected automata -- those are candidates for product
    // compute a product

    // schedule both terms for removal
    // add the product from scratch

    Seq()
  }

  // TODO make this a PredicateHandlingProcedure
  private def handleConnectedInstance(
      connectedInstance: Atom,
      transitionMasks: Seq[Atom],
      goal: Goal
  ) = trace(s"handleConnectedInstance ${connectedInstance}") {

    val autId = connectedAutId(connectedInstance)
    val myTransitionMasks = transitionMasks
      .filter(automataNr(_) == autId)
      .sortBy(transitionNr)
      .toIndexedSeq

    val transitionTerms = trace(s"transition Terms for aut ID ${autId}")(
      myTransitionMasks
        .map(transitionTerm)
    )

    val instanceTerm = connectedInstance(0)

    implicit val order = goal.order
    val aut = auts(autId)
    val autGraph = aut.toGraph
    val transitionToTerm = aut.transitions.zip(transitionTerms.iterator).toMap

    // TODO: we don't care about splitting edges that cannot possibly cause a
    // disconnect; i.e. *we only care* about critical edges on the path to
    // some cycle that can still appear (i.e. wose edges are not
    // known-deselected).

    // TODO experiment with branching order and start close to initial
    // states.

    // TODO compute a cut to find which dead transitions contribute to the conflict!

    val splittingActions = trace("splittingActions") {
      val splitter = new TransitionSplitter(transitionExtractor, theoryInstance)

      goalState(goal) match {
        case Plugin.GoalState.Final => splitter.handleGoal(goal)
        case _                      => List(Plugin.ScheduleTask(splitter, 0))
      }
    }

    val deadTransitions = trace("deadTransitions") {
      aut.transitions
        .filter(
          t => termMeansDefinitelyAbsent(goal, transitionToTerm(t))
        )
        .toSet
    }

    val knownUnreachableEdges = trace("knownUnreachableEdges") {
      autGraph
        .dropEdges(deadTransitions)
        .unreachableFrom(aut.initialState)
    }

    // val maybeDeadTransitions = trace("maybeDeadTransitions") {
    //   aut.transitions.filter(
    //     t => termMeansPossiblyAbsent(goal, transitionToTerm(t))
    //   ).toSet
    // }
    // val possiblyUnreachableEdges = trace("possiblyUnreachableEdges") {
    //   autGraph
    //     .dropEdges(maybeDeadTransitions)
    //     .unreachableFrom(aut.initialState)
    // }
    // FIXME why doesn't this work for subsumption? possiblyUnreachableEdges.isEmpty
    // FIXME: something about splitting?

    val allTransitionsAssigned = transitionTerms.isEmpty || !(transitionTerms exists (
        t => transitionStatusFromTerm(goal, t).isUnknown
    ))

    val subsumeActions =
      if (allTransitionsAssigned) Seq(Plugin.RemoveFacts(connectedInstance))
      else Seq()

    // constrain any terms associated with a transition from a
    // *known* unreachable state to be = 0 ("not used").
    val unreachableActions = trace("unreachableActions") {
      val unreachableConstraints =
        conj(
          knownUnreachableEdges
            .flatMap(
              autGraph.transitionsFrom(_).map(transitionToTerm(_) === 0)
            )
        )

      if (unreachableConstraints.isTrue) Seq()
      else
        Seq(
          Plugin.AddAxiom(
            myTransitionMasks :+ connectedInstance, // FIXME add deadTransitions transitionMask:s
            unreachableConstraints,
            theoryInstance
          )
        )
    }

    unreachableActions ++ splittingActions ++ subsumeActions

  }
  // materialize the nth level product modulo transitionTerms
  private def materialiseProducts(
      transitionTerms: Seq[LinearCombination],
      currentProductDepth: Int
  ): Automaton = ???

}
