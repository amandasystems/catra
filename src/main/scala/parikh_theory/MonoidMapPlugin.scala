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
import EdgeWrapper._
import VariousHelpers.simplifyUnlessTimeout

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
    transitionStatusFromTerm,
    termMeansDefinitelyAbsent,
    termMeansDefinitelyPresent,
    goalAssociatedPredicateInstances,
    transitionNr,
    transitionTerm,
    autId => autNr
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
    trace("handlePredicateInstance") {
      val context = Context(goal, predicateAtom)
      stats.increment("handlePredicateInstance")

      handleMonoidMapSubsumption(context) elseDo
      handleConnectedInstances(context)   elseDo
      handleMaterialise(context)          elseDo
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
      val allAutomataGuaranteedConnected = connectedInstances.isEmpty
      val isSubsumed =
        trace("isSubsumed")(productIsDone && allAutomataGuaranteedConnected)

      if (isSubsumed) {
        // There will be a final Unused predicate on the final automaton.
        val removeAssociatedPredicates =
          unusedInstances.map(Plugin.RemoveFacts(_))
        val removeThisPredicateInstance =
          Plugin.RemoveFacts(monoidMapPredicateAtom)

        stats.report()

        // This cast is necessary to make the code compile because Scala cannot
        // figure out that these two instances of associated types are the same at
        // the current stage. In general, these problems are a sign that the
        // architecture is not fully sound, and that we should perhaps not use
        // callbacks (or associated types) this way. Please send help.
        theoryInstance.actionHook(
          context.asInstanceOf[this.theoryInstance.monoidMapPlugin.Context],
          "Subsume",
          Seq()
        )

        removeAssociatedPredicates :+ removeThisPredicateInstance
      } else {
        Seq()
      }
    }

  private def handleSplitting(context: Context) = trace("handleSplitting") {
    stats.increment("handleSplitting")

//    val splitter = new TransitionSplitter()

    goalState(context.goal) match {
      case Plugin.GoalState.Final => new TransitionSplitter().handleGoal(context.goal)
      case _                      => Seq() // Only split when we have to!
    }
  }

  private def handleMaterialise(context: Context) : Seq[Plugin.Action] = trace("handleMaterialise") {
    val knownConnectedAutomataNrs: Seq[Int] =
      trace("knownConnectedAutomataNrs")(
        context.activeAutomata
          .diff(context.automataWithConnectedPredicate)
          .toSeq
      )

    val rand =
      ap.parameters.Param.RANDOM_DATA_SOURCE(context.goal.settings)

    knownConnectedAutomataNrs match {
      case Seq()  => Seq()
      case Seq(fst) => {
        val otherAutomata = context.activeAutomata.toSeq filterNot (_ == fst)
        if (otherAutomata.isEmpty) {
          Seq()
        } else {
          // TOOD: what is better, pick the second automaton randomly,
          // or take the smallest one?

          val snd = otherAutomata(rand nextInt otherAutomata.size)
//          val otherSorted =
//            otherAutomata.sortBy(context.filteredAutomaton(_).states.size)
//          val snd =
//            otherSorted.head
          materialiseProduct(fst, snd, context)
        }
      }
      case Seq(left, right) =>
        materialiseProduct(left, right, context)
      case nrs => {
        val buf = nrs.toBuffer
        rand.shuffle(buf)
        val sort = buf.toSeq.take(2).sorted
        materialiseProduct(sort(0), sort(1), context)
      }
    }

  }

  private def handleMaterialiseOld(context: Context) = trace("handleMaterialise") {
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
      case _ =>
        throw new IllegalArgumentException(
          knownConnectedAutomataNrs mkString ","
        )
    }
  }

  private def handleConnectedInstances(context: Context) =
    context.connectedInstances
      .flatMap(handleConnectedInstance(_, context))

  // TODO make this a PredicateHandlingProcedure?
  private def handleConnectedInstance(
      connectedInstance: Atom,
      context: Context
  ): Seq[Plugin.Action] =
    trace(s"handleConnectedInstance ${connectedInstance}") {

      val autId = autNr(connectedInstance)
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
        aut.transitions forall { t => deadTransitions(t) || definitelyReached(t._1) }

      val subsumeActions =
        if (allTransitionsAssigned) {
          // This cast is necessary to make the code compile because Scala cannot
          // figure out that these two instances of associated types are the same at
          // the current stage. In general, these problems are a sign that the
          // architecture is not fully sound, and that we should perhaps not use
          // callbacks (or associated types) this way. Please send help.
          theoryInstance.actionHook(
            context.asInstanceOf[this.theoryInstance.monoidMapPlugin.Context],
            "SubsumeConnected",
            Seq()
          )

          Seq(Plugin.RemoveFacts(connectedInstance))

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
          val actions = Seq(
            Plugin.AddAxiom(
              myTransitionMasks :+ connectedInstance, // FIXME limit to deadTransitions transitionMask:s
              unreachableConstraints,
              theoryInstance
            )
          )
          // This cast is necessary to make the code compile because Scala cannot
          // figure out that these two instances of associated types are the same at
          // the current stage. In general, these problems are a sign that the
          // architecture is not fully sound, and that we should perhaps not use
          // callbacks (or associated types) this way. Please send help.
          theoryInstance.actionHook(
            context.asInstanceOf[this.theoryInstance.monoidMapPlugin.Context],
            "Propagate-Connected",
            actions
          )
          actions
        }
      }

      unreachableActions ++ subsumeActions

    }

  private def materialiseProduct(
      leftId: Int,
      rightId: Int,
      context: Context
  ) = trace(s"materialise ${leftId}x${rightId}") {
    stats.increment("materialiseProduct")

    // This cast is necessary to make the code compile because Scala cannot
    // figure out that these two instances of associated types are the same at
    // the current stage. In general, these problems are a sign that the
    // architecture is not fully sound, and that we should perhaps not use
    // callbacks (or associated types) this way. Please send help.
    theoryInstance.actionHook(
      context.asInstanceOf[this.theoryInstance.monoidMapPlugin.Context],
      "MaterialiseProduct",
      Seq()
    )

    val left = context.filteredAutomaton(leftId)
    val right = context.filteredAutomaton(rightId)

    trace(
      s"materialising product of ${left} and ${right}"
    )("")

    val annotatedProduct = left.productWithSources(right)
    val product = annotatedProduct.product

    val newAutomataNr = trace("newAutomataNr")(materialisedAutomata.size)
    materialisedAutomata += product

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

    // TODO figure out how to generate a nice blocking clause to replace FALSE
    val productClauses = if (trace("product is empty")(product.isEmpty)) {
      Seq(
        Plugin.AddAxiom(
          unusedInstances ++ context.autTransitionMasks(leftId) ++ context
            .autTransitionMasks(
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

    removeUnusedPredicates ++ productClauses
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
    val transitionToTermSeq = trace("product transitionToTerm")(
      materialisedAutomata(productNr).transitions
        .map(t => (t, varFactory.nextVariable()))
        .toIndexedSeq
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
          val originTerm =
            if (autNr == leftNr) TermOrigin.Left else TermOrigin.Right

          def productTermsSum(t: Transition) = trace(s"${autNr}::${t}Σ") {
            annotatedProduct.resultsOf(originTerm)(t) match {
              case Some(productTransitions) =>
                lcSum(productTransitions.map(productTransitionToLc))
              case None => l(ZERO)
            }
          }

          materialisedAutomata(autNr).transitions.map(
            termTransition =>
              trace(s"a${autNr} bridge: ${termTransition}")(
                trace("LHS")(transitionToTerm(termTransition)) === trace("RHS")(
                  productTermsSum(termTransition)
                )
              )
          )
        }
      )

    }

    val equations = varFactory.exists(conj(newClauses ++ bridgingClauses))
    val simplifiedEquations = simplifyUnlessTimeout(order, equations)

    Seq(
      Plugin.RemoveFacts(conj((context.connectedInstances filter {
                                 a => Set(leftNr,
                                          rightNr) contains a(1).constant.intValueSafe
                               }) ++
                                context.autTransitionMasks(leftNr) ++
                                context.autTransitionMasks(rightNr))),
      Plugin.AddAxiom(
        context.autTransitionMasks(leftNr) ++ context.autTransitionMasks(
          rightNr
        ) :+ context.monoidMapPredicateAtom,
        simplifiedEquations,
        theoryInstance
      )
    )

  }

  /**
   * This class captures common contextual values that can be extracted from a
   * proof goal.
   */
  sealed case class Context(val goal: Goal, val monoidMapPredicateAtom: Atom) {
    import theoryInstance.{
      transitionMaskPredicate => TransitionMask,
      unusedPredicate => Unused,
      connectedPredicate => Connected
    }
    val instanceTerm = monoidMapPredicateAtom(0)
    implicit val order = goal.order

    private val transitionTermCache = HashMap[Int, Map[Transition, Term]]()

    private val predicateInstances =
      goalAssociatedPredicateInstances(goal, instanceTerm)(_)

    lazy val connectedInstances =
      trace("connectedInstances")(predicateInstances(Connected))

    lazy val automataWithConnectedPredicate = SortedSet(
      connectedInstances.map(autNr): _*
    )

    lazy val transitionMasks =
      trace("transitionMasks")(predicateInstances(TransitionMask))

    lazy val unusedInstances =
      trace("unusedInstances")(predicateInstances(Unused))

    lazy val activeAutomata =
      trace("activeAutomata")(SortedSet(unusedInstances.map(autNr): _*))

    // FIXME memoise
    def transitionStatus(autId: Int)(transition: Transition) =
      transitionStatusFromTerm(goal, l(autTransitionTerm(autId)(transition)))

    def getOrUpdateTransitionTermMap(autId: Int) = {
      val autMap: Map[Transition, Term] =
        transitionTermCache.getOrElseUpdate(
          autId,
          trace(s"getOrUpdateTransitionTermMap::materialise(aut=${autId})")(
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
    def autTransitionMasks(autId: Int) = {
      transitionMasks
        .filter(autNr(_) == autId)
        .sortBy(transitionNr)
        .toIndexedSeq
    }

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
        context.automataWithConnectedPredicate.toSeq
          .flatMap { aNr =>
            materialisedAutomata(aNr)
              .transitionsBreadthFirst()
              .filter(
                context.transitionStatus(aNr)(_).isUnknown
              )
              .map(context.autTransitionTerm(aNr))
          }
      }

      def transitionToSplit(tTerm: LinearCombination) =
        Plugin.AxiomSplit(
          Seq(),
          Seq(tTerm <= 0, tTerm > 0).map(ineq => (conj(ineq), Seq())),
          theoryInstance
        )

      val rand = ap.parameters.Param.RANDOM_DATA_SOURCE(goal.settings)
      val allSplits = unknownTransitions.map(transitionToSplit(_)).toSeq
      val split =
        if (allSplits.isEmpty)
          List()
        else
          List(allSplits(rand nextInt allSplits.size))

      // This cast is necessary to make the code compile because Scala cannot
      // figure out that these two instances of associated types are the same at
      // the current stage. In general, these problems are a sign that the
      // architecture is not fully sound, and that we should perhaps not use
      // callbacks (or associated types) this way. Please send help.
      theoryInstance.actionHook(
        context.asInstanceOf[theoryInstance.monoidMapPlugin.Context],
        "Split",
        split
      )

      split
    }
  }

  def dumpGraphs(
      context: Context,
      fileNamePrefix: String = s"${this.theoryInstance.filePrefix}"
  ) = {
    materialisedAutomata.zipWithIndex.map {
      case (a, i) =>
        new GraphvizDumper {
          // NOTE: this is a brittle mapping since it will break silently if the
          // order in ParikhTheory.automataClauses changes...
          val transitionToIdx = a.transitions.zipWithIndex.toMap

          private def markTransitionTerms(t: Transition) = {
            // This is necessary because we might be called after all
            // TransitionMask predicates are eliminated, which means that we do
            // not have any information about the labelling.
            val transitionTermMap = context.getOrUpdateTransitionTermMap(i)
            val term = transitionTermMap.get(t).getOrElse("No term")
            s"${t.label()}: ${transitionToIdx(t)}/$term"
          }

          def toDot() = a.toDot(
            transitionAnnotator = markTransitionTerms _,
            stateAnnotator = _.toString()
          )

        }.dumpDotFile(fileNamePrefix + s"-aut-${i}.dot")
        fileNamePrefix + s"-aut-${i}.dot"
    }.toSeq
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
