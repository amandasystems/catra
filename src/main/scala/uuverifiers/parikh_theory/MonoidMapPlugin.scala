package uuverifiers.parikh_theory
import ap.parameters.Param
import ap.parser.IExpression.Predicate
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TerForConvenience._
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.preds.Atom
import uuverifiers.common._

import java.io.File
import scala.collection.mutable.ArrayBuffer
import scala.collection.{BitSet, mutable}

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

  // bitvector for selected left bitvector for selected right, left id, right id
  private val productFingerprintToId =
    mutable.HashMap[(BitSet, BitSet, Int, Int), Int]()

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

      if (Param.MODEL_GENERATION(context.goal.settings)) {
//        println("model generation, doing nothing")
//        println(goal.facts)
        return List()
      }

      handleMonoidMapSubsumption(context) elseDo
        handleConnectedInstances(context) elseDo
        TransitionSplitter.spawnSplitters(goal, theoryInstance) elseDo
        handleMaterialise(context)
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

  /*
  private def handleSplitting(context: Context) = trace("handleSplitting") {
    stats.increment("handleSplitting")

    goalState(context.goal) match {
      case Plugin.GoalState.Final =>
        TransitionSplitter(theoryInstance).handleGoal(context.goal)
      case _ => Seq() // Only split when we have to!
    }
  }
   */

  private def chooseAutomataForMaterialisation(
      context: Context
  ): Option[(Int, Int)] = {
    val consideredAutomata =
      for (a <- context.activeAutomata.toSeq
           if context.isConnected(a) ||
             context.nrUnknownTransitions(a) <= theoryInstance.materialisationThreshold)
        yield a

    def complexityThenIndex(a: Int) =
      (
        context
          .nrUniqueTerms(a)
          .size,
        a
      )

    val consideredAutomataSorted =
      consideredAutomata.sortBy(complexityThenIndex)

    consideredAutomataSorted match {
      case Seq(fst, snd, _*) => Some((fst, snd))
      case _                 => None
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

  private def explainUnreachability(
      deadTransitions: Set[Transition],
      context: Context,
      connectedInstance: Atom
  ): Seq[Plugin.Action] =
    trace("unreachableActions") {
      val autId = autNr(connectedInstance)
      val aut = materialisedAutomata(autId)
      val transitionToTerm = context.autTransitionTerm(autId)(_)
      implicit val order: TermOrder = context.goal.order

      def conclude(assuming: Seq[Formula], have: Conjunction) = {
        println(s"From $assuming, conclude that $have")
        Seq(Plugin.AddAxiom(assuming, have, theoryInstance))
      }

      val nothingLearned = Seq.empty

      val fwReachable = aut.fwdReachable(deadTransitions) // FIXME

      val finalStates = aut.states.filter(aut.isAccept).toSet
      val noReachableAcceptingState =
        !aut.states.exists(
          s => finalStates.contains(s) && fwReachable.contains(s)
        ) // FIXME use set operations

      // Case 1: total: the automaton accepts no string (no final state is reachable from the initial state)
      if (noReachableAcceptingState) {

        val loadBearingTransitions =
          finalStates
            .flatMap(
              f =>
                aut
                  .minCut(aut.initialState, f)
                  .map(_._2)
            )
            .toSeq
            .distinct

        val loadBearingMasks =
          loadBearingTransitions.map(context.autTransitionMask(autId))

        val cutIsZero = conj(loadBearingMasks.map(_.last <= 0))
        println(s"Total connectivity loss for cut: $cutIsZero") // FIXME
        return Seq(
          Plugin
            .AddAxiom(
              loadBearingMasks :+ cutIsZero,
              conj(connectedInstance).negate,
              theoryInstance
            )
        )
      }

      // FIXME this is a mess of duplicated code!

      // Case 2: forward-unreachable
      val fwConclusions = aut.states
        .filter(!fwReachable.contains(_))
        .flatMap(aut.transitionsFrom)
        .flatMap { t =>
          val tIsUnused = transitionToTerm(t) === 0
          if (tIsUnused.isTrue) return nothingLearned // FIXME don't use return
          val separatingCut = aut
            .minCut(aut.initialState, t.from())
            .map(_._2)
          val cutMasks = separatingCut
            .map(context.autTransitionMask(autId))
            .toSeq
          val cutIsZero = conj(cutMasks.map(_.last <= 0))
          assert(cutIsZero.isTrue, s"Forward cut $cutMasks must be true!")
          println(s"Fw-unreachable cut: $cutMasks for $t")
          conclude(
            assuming = cutMasks :+ context
              .autTransitionMask(autId)(t) :+ connectedInstance,
            have = tIsUnused
          )
        }

      val bwdReachable = aut.bwdReachable(deadTransitions) // FIXME
      // Case 3: backward-unreachable
      val bwConclusions = aut.states
        .filter(!bwdReachable.contains(_))
        .flatMap(aut.transitionsFrom)
        .flatMap { t =>
          val tIsUnused = transitionToTerm(t) === 0
          if (tIsUnused.isTrue) return Seq() // FIXME don't use return
          val autReversed = aut.reverseGraph()
          val separatingCut = aut.states
            .filter(aut.isAccept)
            .flatMap(
              as =>
                autReversed
                  .minCut(as, t.from())
                  .map(_._2)
            )
          val cutMasks = separatingCut
            .map(context.autTransitionMask(autId))
            .toSeq
          val cutIsZero = conj(cutMasks.map(_.last <= 0))
          assert(cutIsZero.isTrue, s"Backward cut $cutMasks must be true!")
          println(s"Bw-unreachable cut: $cutMasks for $t")
          conclude(
            assuming = cutMasks :+ context
              .autTransitionMask(autId)(t) :+ connectedInstance,
            have = tIsUnused
          )
        }

      (fwConclusions ++ bwConclusions).toSeq
    }

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
      }.toSeq

      val definitelyReached = trace("definitelyReached")(
        aut.fwdReachable(aut.transitions.toSet -- presentTransitions)
      )

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

      val unreachableTransitions =
        knownUnreachableStates.flatMap(aut.transitionsFrom(_))

      // constrain any terms associated with a transition from a
      // *known* unreachable state to be = 0 ("not used").
      val unreachableActions = {
        val actions =
          conj(unreachableTransitions.map(transitionToTerm(_) === 0)) match {
            case c if c.isTrue => Seq()
            case _
                if ap.parameters.Param.PROOF_CONSTRUCTION(
                  context.goal.settings
                ) =>
              explainUnreachability(
                deadTransitions,
                context,
                connectedInstance
              )
            case c =>
              Seq(
                Plugin.AddAxiom(
                  myTransitionMasks :+ connectedInstance,
                  c,
                  theoryInstance
                )
              )
          }
        theoryInstance.runHooks(
          context,
          "Propagate-Connected",
          actions = actions
        )
      }

      unreachableActions ++ subsumeActions
    }

  def getOrComputeProduct(
      leftId: Int,
      rightId: Int,
      context: Context
  ): Int = trace(s"getOrComputeProduct ${leftId}x$rightId") {
    val signature = trace(s"${leftId}x$rightId signature")(
      (
        context.deselectedTransitionSignature(leftId),
        context.deselectedTransitionSignature(rightId),
        leftId,
        rightId
      )
    )

    val productId = productFingerprintToId.getOrElseUpdate(
      signature,
      materialisedAutomata.size
    )
    if (productId == materialisedAutomata.size) {
      val product = trace(s"Computed new product from ${leftId}x$rightId")(
        context
          .filteredAutomaton(leftId) productWith context
          .filteredAutomaton(rightId)
      )
      materialisedAutomata += product
    }

    // Note: we cannot filter the product since it came from a different
    // branch and does not yet have TransitionMasks here!
    productId
  }

  private def materialiseProduct(
      leftId: Int,
      rightId: Int,
      context: Context
  ) = trace(s"materialise ${leftId}x$rightId") {
    stats.increment("materialiseProduct")
    val productNr = getOrComputeProduct(leftId, rightId, context)

    def concernsOneOfTheTerms(p: Atom): Boolean = {
      autNr(p) match {
        case `leftId` | `rightId` => true
        case _                    => false
      }
    }

    val unusedInstances = context.unusedInstances.filter(concernsOneOfTheTerms)
    val removeUnusedPredicates = trace("removeUnusedPredicates")(
      unusedInstances.map(Plugin.RemoveFacts(_))
    )

    val productClauses =
      if (trace(s"$leftId}x$rightId is empty")(
            materialisedAutomata(productNr).isEmpty
          )) {

        def extractAssumptions(id: Int) =
          for (a <- context.autTransitionMasks(id); if a.last.isZero)
            yield a

        val assumptions =
          extractAssumptions(leftId) ++ extractAssumptions(rightId) ++ unusedInstances

        Seq(
          Plugin.AddAxiom(
            assumptions,
            Conjunction.FALSE,
            theoryInstance
          )
        )
      } else {
        TransitionSplitter.spawnSplitter(
          context.theoryInstance,
          context.monoidMapPredicateAtom(0),
          productNr
        ) ++
          formulaForNewAutomaton(
            productNr,
            leftId,
            rightId,
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
      context: Context
  ) = {

    val product = materialisedAutomata(productNr)
    implicit val order: TermOrder = context.goal.order
    val varFactory = new FreshVariables(0)
    val transitionToTermSeq = trace("product transitionToTerm")(
      product.transitions
        .map(t => (t, varFactory.nextVariable()))
    )

    val transitionToTerm = transitionToTermSeq.toMap
    val finalTerms = product.states
      .filter(product.isAccept)
      .map(s => (s, varFactory.nextVariable()))
      .toMap

    val newClauses = theoryInstance.automataClauses(
      product,
      context.instanceTerm,
      productNr,
      finalTerms,
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
    val simplifiedEquations =
      ReduceWithConjunction(Conjunction.TRUE, order)(equations)

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
      )
    ) ++ matActions

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
