package uuverifiers.parikh_theory
import ap.parser.IExpression.Predicate
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TerForConvenience._
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import uuverifiers.common._
import uuverifiers.parikh_theory.VariousHelpers.simplifyUnlessTimeout

import java.io.File
import scala.collection.mutable.ArrayBuffer

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

  private val transitionExtractor = new TransitionMaskExtractor(theoryInstance)

  import transitionExtractor.{
    termMeansDefinitelyAbsent,
    termMeansDefinitelyPresent,
    autId => autNr
  }

  // A cache for materialised automata. The first ones are the same as auts.
  val materialisedAutomata: ArrayBuffer[Automaton] = ArrayBuffer(
    theoryInstance.auts: _*
  )

  override val procedurePredicate: Predicate = theoryInstance.monoidMapPredicate

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
    trace("handlePredicateInstance") {
      val context = Context(goal, predicateAtom, theoryInstance)
      stats.increment("handlePredicateInstance")

      handleMonoidMapSubsumption(context) elseDo
        handleConnectedInstances(context) elseDo
        handleMaterialise(context) elseDo
        handleSplitting(context)
    }

  private def handleMonoidMapSubsumption(
      context: Context
  ) =
    trace("handleMonoidMapSubsumption") {
      import context.{
        activeAutomata,
        connectedInstances,
        monoidMapPredicateAtom,
        unusedInstances
      }

      val productIsDone =
        trace("productIsDone")(activeAutomata.size <= 1)
      val allAutomataGuaranteedConnected = trace(
        "all automata guaranteed to be connected"
      )(connectedInstances.isEmpty)
      val isSubsumed =
        trace("isSubsumed")(productIsDone && allAutomataGuaranteedConnected)

      if (isSubsumed) {
        // There will be a final Unused predicate on the final automaton.
        val removeAssociatedPredicates =
          unusedInstances.map(Plugin.RemoveFacts(_))
        val removeThisPredicateInstance =
          Plugin.RemoveFacts(monoidMapPredicateAtom)

        stats.report()

        theoryInstance.runHooks(
          context,
          "Subsume MonoidMap",
          actions = removeAssociatedPredicates :+ removeThisPredicateInstance
        )
      } else {
        Seq()
      }
    }

  private def handleSplitting(context: Context) = trace("handleSplitting") {
    stats.increment("handleSplitting")

    goalState(context.goal) match {
      case Plugin.GoalState.Final =>
        TransitionSplitter(theoryInstance).handleGoal(context.goal)
      case _ => Seq() // Only split when we have to!
    }
  }

  private def chooseAutomataForMaterialisation(
      context: Context
  ): Option[(Int, Int)] = {
    def aboveThreshold(auts: Seq[Int]): Boolean =
      context.nrUnknownTransitions(auts.head) > theoryInstance.materialisationThreshold

    val automataByNrUnknowns =
      context.activeAutomata.toSeq.sortBy(context.nrUnknownTransitions)

    automataByNrUnknowns match {
      case Nil                          => None
      case auts if aboveThreshold(auts) => None
      case fst +: rest                  => context.chooseRandomly(rest).map(snd => (fst, snd))
    }
  }

  private def handleMaterialise(context: Context): Seq[Plugin.Action] =
    trace("handleMaterialise") {
      chooseAutomataForMaterialisation(context)
        .map { case (left, right) => materialiseProduct(left, right, context) }
        .getOrElse(Seq())
    }

  private def handleConnectedInstances(context: Context) =
    context.connectedInstances
      .flatMap(handleConnectedInstance(_, context))

  private def handleConnectedInstance(
      connectedInstance: Atom,
      context: Context
  ): Seq[Plugin.Action] =
    trace(s"handleConnectedInstance $connectedInstance") {

      val autId = autNr(connectedInstance)
      val myTransitionMasks = context.autTransitionMasks(autId)
      val aut = materialisedAutomata(autId)
      val transitionToTerm = context.autTransitionTerm(autId)(_)

      implicit val order: TermOrder = context.goal.order

      // TODO compute a cut to find which dead transitions contribute to the conflict!

      val deadTransitions = trace("deadTransitions") {
        aut.transitions
          .filter(
            t => termMeansDefinitelyAbsent(context.goal, transitionToTerm(t))
          )
          .toSet
      }

      val presentTransitions = trace("presentTransitions") {
        aut.transitions
          .filter(
            t => termMeansDefinitelyPresent(context.goal, transitionToTerm(t))
          )
          .toSet
      }

      val reachableStates =
        aut.fwdReachable(deadTransitions) & aut.bwdReachable(deadTransitions)
      val knownUnreachableStates = trace("knownUnreachableStates") {
        aut.states filterNot reachableStates
      }

      /*
      val filteredGraph = aut.dropEdges(deadTransitions)

      val knownUnreachableStates = trace("knownUnreachableStates") {
        filteredGraph.unreachableFrom(aut.initialState)
      }

      val unknownEdges = trace("unknownEdges")(
        context.autTransitionTermsUnordered(autId) filter (
            t => transitionStatusFromTerm(context.goal, t).isUnknown
        )
      )
       */

      val definitelyReached =
        aut.fwdReachable(aut.transitions.toSet -- presentTransitions)

      val allTransitionsAssigned =
        trace("all transitions assigned?") {
          aut.transitions forall { t =>
            deadTransitions(t) || definitelyReached(t.from())
          }
        }

      val subsumeActions =
        if (allTransitionsAssigned) {
          theoryInstance.runHooks(
            context,
            "SubsumeConnected",
            actions = Seq(Plugin.RemoveFacts(connectedInstance))
          )
        } else Seq()

      // constrain any terms associated with a transition from a
      // *known* unreachable state to be = 0 ("not used").
      val unreachableActions = trace("unreachableActions") {
        val unreachableTransitions = trace("unreachableTransitions")(
          knownUnreachableStates.flatMap(aut.transitionsFrom(_))
        )
        val unreachableConstraints =
          conj(unreachableTransitions.map(transitionToTerm(_) === 0))

        if (unreachableConstraints.isTrue) Seq() // TODO why not subsume?
        else {

          val acts =
            if (ap.parameters.Param.PROOF_CONSTRUCTION(context.goal.settings)) {

              // FIXME limit to deadTransitions transitionMask:s that actually
              // contribute to the conflict

              for (trans <- unreachableTransitions.toSeq;
                   term = transitionToTerm(trans);
                   constr = (term === 0);
                   if !constr.isTrue;
                   relTransitions = {
                     for (a <- myTransitionMasks;
                          if a.last.isZero || a.last == term)
                     yield a
                   };
                   assumptions = relTransitions :+ connectedInstance) yield {
                Plugin.AddAxiom(assumptions, constr, theoryInstance)
              }

            } else {

              Seq(
                Plugin.AddAxiom(
                  myTransitionMasks :+ connectedInstance,
                  unreachableConstraints,
                  theoryInstance
                )
              )

            }

          theoryInstance.runHooks(
            context,
            "Propagate-Connected",
            actions = acts
          )
        }
      }
      unreachableActions ++ subsumeActions
    }

  private def materialiseProduct(
      leftId: Int,
      rightId: Int,
      context: Context
  ) = trace(s"materialise ${leftId}x$rightId") {
    stats.increment("materialiseProduct")
    val left = context.filteredAutomaton(leftId)
    val right = context.filteredAutomaton(rightId)
    trace(
      s"materialising product of $left and $right"
    )("")

    val product = left.productWith(right)

    // TODO  keep track of automata we have already seen (mapping from
    // transitions set to zero, incoming IDs -> id)
    val newAutomataNr = trace("newAutomataNr")(materialisedAutomata.size)
    materialisedAutomata += product

    def concernsOneOfTheTerms(p: Atom): Boolean = {
      autNr(p) match {
        case `leftId` | `rightId` => true
        case _                    => false
      }
    }

    // TODO filter by the zero-transitions
    val unusedInstances = context.unusedInstances.filter(concernsOneOfTheTerms)
    val removeUnusedPredicates = trace("removeUnusedPredicates")(
      unusedInstances.map(Plugin.RemoveFacts(_))
    )

    // TODO figure out how to generate a nice blocking clause to replace FALSE
    val productClauses = if (trace("product is empty")(product.isEmpty)) {
      val leftMasks =
        for (a <- context.autTransitionMasks(leftId); if a.last.isZero)
        yield a
      val rightMasks =
        for (a <- context.autTransitionMasks(rightId); if a.last.isZero)
        yield a

      val assumptions =
        if (leftMasks.isEmpty || rightMasks.isEmpty)
          leftMasks ++ rightMasks ++ List(context.monoidMapPredicateAtom)
        else
          leftMasks ++ rightMasks

      Seq(
        Plugin.AddAxiom(
          assumptions,
          Conjunction.FALSE,
          theoryInstance
        )
      )
    } else {
      formulaForNewAutomaton(
        newAutomataNr,
        leftId,
        rightId,
        product,
        context
      )

    }

    val actions = removeUnusedPredicates ++ productClauses

    theoryInstance.runHooks(
      context,
      "MaterialiseProduct",
      actions
    )
    actions
  }

  private def formulaForNewAutomaton(
      productNr: Int,
      leftNr: Int,
      rightNr: Int,
      product: Automaton,
      context: Context
  ) = {

    implicit val order: TermOrder = context.goal.order
    val varFactory = new FreshVariables(0)
    val transitionToTermSeq = trace("product transitionToTerm")(
      materialisedAutomata(productNr).transitions
        .map(t => (t, varFactory.nextVariable()))
    )

    val transitionToTerm = transitionToTermSeq.toMap

    val newClauses = theoryInstance.automataClauses(
      materialisedAutomata(productNr),
      context.instanceTerm,
      productNr,
      transitionToTermSeq
    )

    // - x(t) = sum(e : termProductEdges(t, default=0))
    val bridgingClauses = trace("Bridging clauses") {
      val productTransitionToLc = transitionToTerm.andThen(l(_)(order))

      Seq(leftNr, rightNr).flatMap(
        autNr => {
          val transitionToTerm = context.autTransitionTerm(autNr)(_)
          // .get is safe here because we know we are dealing with product transitions!
          def originTerm(pt: ProductTransition): Transition =
            if (autNr == leftNr)
              pt.originTransitions().get._1
            else pt.originTransitions().get._2

          def productTermsSum(termTransition: Transition) =
            trace(s"$autNr::${termTransition}Σ") {
              val resultsOfTransition =
                product.transitions.filter(
                  // FIXME: get rid of this asInstanceOf!
                  pt => originTerm(pt.asInstanceOf[ProductTransition]) == termTransition
                )
              lcSum(
                trace(s"productTransitions of $termTransition")(
                  resultsOfTransition
                ).map(productTransitionToLc)
              )
            }

          materialisedAutomata(autNr).transitions.map(
            termTransition =>
              trace(s"a#$autNr bridge: $termTransition") {
                val termTransitionTerm = transitionToTerm(termTransition)
                val sumOfResultingEdges = productTermsSum(termTransition)
                trace(s"$termTransitionTerm = $sumOfResultingEdges")(
                  termTransitionTerm === sumOfResultingEdges
                )
              }
          )
        }
      )

    }

    val equations = varFactory.exists(conj(newClauses ++ bridgingClauses))
    val simplifiedEquations = simplifyUnlessTimeout(order, equations)

    val assumptions =
      context.autTransitionMasks(leftNr) ++ context.autTransitionMasks(
              rightNr
            ) :+ context.monoidMapPredicateAtom

    // work-around: adding a conjunction of literals (non-quantified)
    // sometimes seems to cause an exception. this must be a bug in
    // princess, to be fixed
    val matActions =
      if (simplifiedEquations.quans.isEmpty)
        (for (lit <- simplifiedEquations.iterator) yield {
           Plugin.AddAxiom(assumptions, lit, theoryInstance)
         }).toList
      else
        List(Plugin.AddAxiom(assumptions, simplifiedEquations, theoryInstance))

    Seq(
      Plugin.RemoveFacts(
        conj(
          (context.connectedInstances filter { a =>
            Set(leftNr, rightNr) contains a(1).constant.intValueSafe
          }) ++
            context.autTransitionMasks(leftNr) ++
            context.autTransitionMasks(rightNr)
        )
      )) ++ matActions

  }

  def dumpGraphs(directory: File): Unit = {
    materialisedAutomata.zipWithIndex.foreach {
      case (a, i) =>
        // TODO extract transition labels and annotate the graph with them
        a.dumpDotFile(
          directory,
          s"monoidMapTheory-${this.theoryInstance.hashCode()}-aut-$i.dot"
        )
    }
  }

}
