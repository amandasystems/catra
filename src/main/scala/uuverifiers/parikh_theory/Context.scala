package uuverifiers.parikh_theory
import ap.terfor.preds.Atom
import ap.terfor.{Term, TermOrder}
import ap.proof.goal.Goal
import ap.terfor.TerForConvenience._
import ap.terfor.linearcombination.LinearCombination

import scala.collection.{SortedSet, mutable}
import uuverifiers.common._

import java.io.File

/**
 * This class captures common contextual values that can be extracted from a
 * proof goal.
 */
sealed case class Context(
    goal: Goal,
    monoidMapPredicateAtom: Atom,
    theoryInstance: ParikhTheory
) extends Tracing {

  private val rand = ap.parameters.Param.RANDOM_DATA_SOURCE(goal.settings)

  def chooseRandomly[A](xs: Seq[A]): Option[A] =
    if (xs.isEmpty) None else Some(xs(rand nextInt xs.size))

  def nrUnknownTransitions(aut: Int): Int =
    materialisedAutomata(aut).transitions
      .count(t => transitionStatus(aut)(t) == TransitionSelected.Unknown)

  def nrUniqueTerms(aut: Int): Int = autTransitionTermsUnordered(aut).toSet.size

  private val transitionExtractor = new TransitionMaskExtractor(theoryInstance)
  import transitionExtractor.{
    transitionStatusFromTerm,
    termMeansDefinitelyAbsent,
    goalAssociatedPredicateInstances,
    transitionNr,
    transitionTerm,
    autId => autNr
  }

  /**
   * Summarise what is going on.
   *
   * @return
   */
  def summarise(): String = {
    val automata = activeAutomata.mkString(", ")
    val predicates =
      (transitionMasks ++ unusedInstances ++ connectedInstances).mkString(", ")

    s"Context: active automata: $automata, predicates: $predicates"
  }

  private val materialisedAutomata =
    theoryInstance.monoidMapPlugin.materialisedAutomata

  import theoryInstance.{
    transitionMaskPredicate => TransitionMask,
    unusedPredicate => Unused,
    connectedPredicate => Connected
  }
  val instanceTerm: LinearCombination = monoidMapPredicateAtom(0)
  implicit val order: TermOrder = goal.order

  private val transitionTermCache =
    mutable.HashMap[Int, Map[Transition, Term]]()

  private val predicateInstances =
    goalAssociatedPredicateInstances(goal, instanceTerm)(_)

  lazy val connectedInstances: Seq[Atom] =
    trace("connectedInstances")(predicateInstances(Connected))

  lazy val automataWithConnectedPredicate: SortedSet[Int] = SortedSet(
    connectedInstances.map(autNr): _*
  )

  lazy val unusedInstances: Seq[Atom] =
    trace("unusedInstances")(predicateInstances(Unused))

  lazy val transitionMasks: Seq[Atom] =
    trace("transitionMasks")(predicateInstances(TransitionMask))

  lazy val activeAutomata: SortedSet[Int] =
    trace("activeAutomata")(SortedSet(unusedInstances.map(autNr): _*))

  // FIXME memoise
  def transitionStatus(autId: Int)(transition: Transition): TransitionSelected =
    transitionStatusFromTerm(goal, l(autTransitionTerm(autId)(transition)))

  def getOrUpdateTransitionTermMap(autId: Int): Map[Transition, Term] = {
    val autMap: Map[Transition, Term] =
      transitionTermCache.getOrElseUpdate(
        autId,
        trace(s"getOrUpdateTransitionTermMap::materialise(aut=$autId)")(
          materialisedAutomata(autId).transitions
            .zip(autTransitionMasks(autId).map(transitionTerm).iterator)
            .toMap
        )
      )
    autMap
  }

  def autTransitionTerm(autId: Int)(transition: Transition): Term =
    getOrUpdateTransitionTermMap(autId)(transition)

  def autTransitionTermsUnordered(autId: Int): Iterable[Term] =
    getOrUpdateTransitionTermMap(autId).values

  // FIXME memoise
  def autTransitionMasks(autId: Int): Seq[Atom] = {
    transitionMasks
      .filter(autNr(_) == autId)
      .sortBy(transitionNr)
  }

  // FIXME excellent candidate for memoisation!
  def filteredAutomaton(autId: Int): Automaton =
    materialisedAutomata(autId).filterTransitions(
      t =>
        !termMeansDefinitelyAbsent(
          goal,
          l(autTransitionTerm(autId)(t))(goal.order)
        )
    )

  val monoidValues: IndexedSeq[LinearCombination] = monoidMapPredicateAtom.tail

  def dumpGraphs(
      directory: File,
      fileNamePrefix: String = s"${theoryInstance.filePrefix}"
  ): Seq[String] = {
    materialisedAutomata.zipWithIndex.map {
      case (a, i) =>
        new GraphvizDumper {
          // NOTE: this is a brittle mapping since it will break silently if the
          // order in ParikhTheory.automataClauses changes...
          private val transitionToIdx: Map[Transition, Int] =
            a.transitions.zipWithIndex.toMap

          private def markTransitionTerms(t: Transition) = {
            // This is necessary because we might be called after all
            // TransitionMask predicates are eliminated, which means that we do
            // not have any information about the labelling.
            val transitionTermMap = getOrUpdateTransitionTermMap(i)
            val term = transitionTermMap.getOrElse(t, "No term")
            s"${t.label()}: ${transitionToIdx(t)}/$term"
          }

          def toDot(): String = a.toDot(
            transitionAnnotator = markTransitionTerms _,
            stateAnnotator = _.toString()
          )

        }.dumpDotFile(directory, fileNamePrefix + s"-aut-$i.dot")
        fileNamePrefix + s"-aut-$i.dot"
    }.toSeq
  }

}
