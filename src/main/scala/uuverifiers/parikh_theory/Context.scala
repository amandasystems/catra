package uuverifiers.parikh_theory
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TerForConvenience.{conj, lcSum}
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import uuverifiers.catra.Memoiser
import uuverifiers.common._

import java.io.File
import scala.collection.{BitSet, SortedSet, mutable}
import scala.util.Try

/**
 * This class captures common contextual values that can be extracted from a
 * proof goal.
 */
sealed case class Context(
    goal: Goal,
    monoidMapPredicateAtom: Atom,
    theoryInstance: ParikhTheory
) extends Tracing {

  def autTransitionMask(autId: Int)(transition: Transition): Atom =
    autTransitionMasks(autId)(
      materialisedAutomata(autId).transitions.indexOf(transition)
    )

  def deselectedTransitionSignature(autId: Int): BitSet = {
    val definitelyDeselected =
      mutable.BitSet(materialisedAutomata(autId).transitions.size)

    materialisedAutomata(autId).transitions.zipWithIndex
      .filter(tAndId => transitionStatus(autId)(tAndId._1).definitelyAbsent)
      .map(_._2)
      .foreach(tId => definitelyDeselected += tId)

    definitelyDeselected.toImmutable
  }

  /** True if the sum of terms is known to be positive (in our case: that
   *  at least one is positive since all terms are at non-negative)
   **/
  def knownPositive(terms: Set[LinearCombination]): Boolean =
    goal.reduceWithFacts
      .lowerBound(lcSum(terms))
      .exists(_ > 0)

  /** True if autId has no Connected predicate, false otherwise **/
  def isConnected(autId: Int): Boolean =
    !(automataWithConnectedPredicate contains autId)

  private val rand = ap.parameters.Param.RANDOM_DATA_SOURCE(goal.settings)

  def shuffle[A](xs: Iterable[A]): Iterable[A] = {
    val buf = xs.toBuffer
    rand.shuffle(buf)
    buf
  }

  def binarySplit(proposition: Conjunction): Plugin.Action =
    Plugin.CutSplit(conj(proposition), List(), List())

  def chooseRandomly[A](xs: Seq[A]): Option[A] =
    if (xs.isEmpty) None else Some(xs(rand nextInt xs.size))

  def nrUnknownTransitions(aut: Int): Int =
    materialisedAutomata(aut).transitions
      .count(t => transitionStatus(aut)(t) == TransitionSelected.Unknown)

  def nrUniqueTerms(aut: Int): Int =
    ttCache.remember(aut)(computeTransitionMaskMap(aut)).values.toSet.size

  private val transitionExtractor = new TransitionMaskExtractor(theoryInstance)
  import transitionExtractor.{
    goalAssociatedPredicateInstances,
    termMeansDefinitelyAbsent,
    transitionNr,
    transitionStatusFromTerm,
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

  private val statusCache =
    new Memoiser[(Int, Transition), TransitionSelected]()

  def transitionStatus(autId: Int)(transition: Transition): TransitionSelected =
    statusCache.remember((autId, transition))(
      transitionStatusFromTerm(goal, autTransitionTerm(autId)(transition))
    )

  private val ttCache = new Memoiser[Int, Map[Transition, LinearCombination]]()

  private def computeTransitionMaskMap(autId: Int) =
    materialisedAutomata(autId).transitions
      .zip(autTransitionMasks(autId).map(transitionTerm).iterator)
      .toMap

  def autTransitionTerm(autId: Int)(transition: Transition): LinearCombination =
    ttCache.remember(autId)(computeTransitionMaskMap(autId))(transition)

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
          autTransitionTerm(autId)(t)
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
            val term = Try {
              autTransitionTerm(i)(t)
            }.map(_.toString).getOrElse("No term")
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
