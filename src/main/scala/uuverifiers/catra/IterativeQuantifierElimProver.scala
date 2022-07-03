
package uuverifiers.catra

import ap.terfor.{Formula, TermOrder, TerForConvenience}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction}
import ap.proof._
import ap.proof.goal._
import ap.proof.tree._
import ap.proof.theoryPlugins.PluginSequence
import ap.util.{Debug, Seqs, Timeout}
import ap.parameters.{GoalSettings, Param}
import ap.theories.Theory

object IterativeQuantifierElimProver {
  private val AC = Debug.AC_PROVER
}

/**
 * Prover to compute a full Parikh image iteratively.
 */
class IterativeQuantifierElimProver(theories : Seq[Theory],
                                    baseOrder : TermOrder) {

  private val simplifier = ConstraintSimplifier.NO_SIMPLIFIER
  private val qeSimplifier = ConstraintSimplifier.LEMMA_SIMPLIFIER
  private val ptf = new SimpleProofTreeFactory(true, simplifier)

  private val randomDataSource = new SeededRandomDataSource(123)

  private val goalSettings = {
    var s = GoalSettings.DEFAULT
    s = Param.CONSTRAINT_SIMPLIFIER.set(s, simplifier)
    s = Param.FUNCTIONAL_PREDICATES.set(
      s, (for (t <- theories.iterator;
               p <- t.functionalPredicates.iterator) yield p).toSet)
    s = Param.SINGLE_INSTANTIATION_PREDICATES.set(
      s,
      (for (t <- theories.iterator;
            p <- t.singleInstantiationPredicates.iterator) yield p).toSet)
    s = Param.THEORY_PLUGIN.set(
      s, PluginSequence(for (t <- theories; p <- t.plugin.toSeq) yield p))
    s = Param.RANDOM_DATA_SOURCE.set(s, randomDataSource)
    s = Param.FULL_SPLITTING.set(s, false)
    s
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def apply(inputFor : Formula) : Conjunction = {
    val order = baseOrder
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IterativeQuantifierElimProver.AC,
                    ((Conjunction collectQuantifiers inputFor) subsetOf Set(Quantifier.ALL)) &&
                    (order isSortingOf inputFor))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val goal = Goal(List(Conjunction.conj(inputFor, order)), Set(),
                    Vocabulary(order), goalSettings)
    expandProof(goal, List(), 0)
  }

  private def checkPruning(goal : Goal) =
    goal.tasks.max match {
      case _ : WrappedFormulaTask => { assert(false); true } // should currently not happen
      case task : BetaFormulaTask => !task.addToQFClauses
      case OmegaTask => OmegaTask.splittingNecessary(goal)
      case EliminateFactsTask => true
      case _ => false
    }

  private def reduceConstraint(c : Conjunction, order : TermOrder) =
    if (c.isTrue || c.isFalse)
      c
    else
      ReduceWithConjunction(Conjunction.TRUE, order)(c)
  
  private def expandProof(tree : ProofTree,
                          collectedConstraints : List[Conjunction],
                          depth : Int) : Conjunction = {
    Timeout.check

    if (!tree.stepPossible) {
//      println("found goal that cannot be extended")
      val goal = tree.asInstanceOf[Goal]
      val allForsDisjunction =
        Conjunction.disj(tree.closingConstraint :: collectedConstraints,
                         tree.order)

      goal definedSyms allForsDisjunction
    } else tree match { 
      case goal : Goal =>
        expandProof(goal.step(ptf), collectedConstraints, depth)

      case WeakenTree(disjunct, subtree) =>
        expandProof(subtree, disjunct :: collectedConstraints, depth)

      case QuantifiedTree(Quantifier.ALL, consts, subtree) => {
        val res = expandProof(subtree, collectedConstraints, depth)
        // Due to the uninterpreted predicates in proof goals, it can
        // happen that some of the quantified constants still occur in
        // the returned constraints. In that case we explicitly
        // eliminate them.
        if (Seqs.disjointSeq(res.constants, consts)) {
          res
        } else {
          implicit val order = subtree.order
          import TerForConvenience._
          val quantRes = forall(consts.toSeq.sortBy(_.name), res)
          qeSimplifier(quantRes, order)
        }
      }

      case tree : AndTree => {
        val leftRes =
          expandProof(tree.left, collectedConstraints, depth + 1)
        if (leftRes.isTrue) {
          expandProof(tree.right, collectedConstraints, depth + 1)
        } else {
          leftRes
        }
      }
      
    }
  }
  
}
