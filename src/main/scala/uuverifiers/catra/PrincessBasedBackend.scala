package uuverifiers.catra

import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Conjunction
import ap.parser._
import uuverifiers.common.Tracing
import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer
import scala.util.Try

object PrincessBasedBackend {

  /**
   * It is more efficient to skolemize formulas before sending them to
   * the prover. This way, learnt lemmas can be kept during restarts.
   */
  class SkolemizingVisitor(p : SimpleAPI)
        extends CollectingVisitor[(List[ITerm], Int, Int),
                                  IExpression] {
    import IExpression._

    def apply(t : IExpression) : IExpression = this.visit(t, (List(), 0, 1))

    override def preVisit(t : IExpression,
                          ctxt : (List[ITerm], Int, Int)) : PreVisitResult = {
      val (subst, shift, polarity) = ctxt

      t match {
        case t : IVariable => {
          ShortCutResult(if (t.index >= subst.size)
                           t shiftedBy shift
                         else
                           subst(t.index))
        }
        case _ : INot => {
          UniSubArgs((subst, shift, -polarity))
        }
        case IBinFormula(IBinJunctor.Eqv, _, _) | _ : IFunApp | _ : IAtom => {
          UniSubArgs((subst, shift, 0))
        }
        case ISortedQuantified(q, sort, f)
            if (polarity == 1 && q == Quantifier.EX) ||
               (polarity == -1 && q == Quantifier.ALL) => {
          val newConst = p.createConstant(sort)
          TryAgain(f, (newConst :: subst, shift - 1, polarity))
        }
        case t : IVariableBinder => {
          val newSubst = for (t <- subst) yield VariableShiftVisitor(t, 0, 1)
          UniSubArgs((ISortedVariable(0, t.sort) :: newSubst, shift, 0))
        }
        case _ => KeepArg
      }
    }

    def postVisit(t : IExpression,
                  ctxt : (List[ITerm], Int, Int),
                  subres : Seq[IExpression]) : IExpression = {
      t update subres
    }

  }

  def skolemize(f : IFormula)(p : SimpleAPI) : IFormula = {
    val visitor = new SkolemizingVisitor(p)
    visitor(f).asInstanceOf[IFormula]
  }

}

/**
 * A helper to construct backends that perform some kind of setup on the
 * Princess theorem prover and then calls the standard check-SAT features.
 */
trait PrincessBasedBackend extends Backend with Tracing {

  val arguments: CommandLineOptions

  /**
   * Essentially performs all the logic common to both modes of operation.
   *
   * @param p A solver instance to use.
   * @param instance
   * @return A mapping from the instance's counters to their corrsponding
   * constants defined in p.
   */
  def prepareSolver(
      p: SimpleAPI,
      instance: Instance
  ): Map[Counter, ConstantTerm]

  // hack to collect all formulas sent to the prover
  val formulasInSolver = new ArrayBuffer[Conjunction]

  @tailrec
  private def luby(i: Int): Int = {
    if ((i & (i + 1)) == 0) {
      (i + 1) / 2
    } else {
      var x = 1
      while (i > 2 * x - 1) x = x * 2
      luby(i - x + 1)
    }
  }

  private def geometric(i : Int) : Double = {
    val r = 1.1
    var res = 1.0
    for (_ <- 0 until i)
      res = res * r
    res
  }

  private def checkSat(p: SimpleAPI): ProverStatus.Value =
    if (arguments.enableRestarts && arguments.backend == ChooseLazy)
      checkSatWithRestarts(p)
    else
      p.checkSat(block = true)

  @tailrec
  private def checkSatWithRestarts(
      p: SimpleAPI,
      iteration: Int = 1
  ): ProverStatus.Value = {
    val runtime = luby(iteration) // geometric(iteration)
    val timeout: Long = (runtime * arguments.restartTimeoutFactor).toLong
    ap.util.Timeout.check
    p.checkSat(block = false)

    p.getStatus(timeout) match {
      case ProverStatus.Running =>
        p.stop(block = true)
        if (arguments.printDecisions) System.err.println("Restart!")
        checkSatWithRestarts(p, iteration = iteration + 1)
      case r => r
    }
  }

  private def checkSolutions(p: SimpleAPI, instance: Instance)(
      counterToSolverConstant: Map[Counter, ConstantTerm]
  ): SatisfactionResult = {
    trace("final sat status")(checkSat(p)) match {
      case ProverStatus.Sat | ProverStatus.Valid =>
        Sat(
          instance.counters
            .map(
              c => c -> p.eval(counterToSolverConstant(c)).bigIntValue
            )
            .toMap
        )
      case ProverStatus.Unsat => {
        if (arguments.printProof)
          println(
            s"Certificate: ${p.certificateAsString(Map(), ap.parameters.Param.InputFormat.Princess)}"
          )

/*
        for (t <- p.theories) t match {
          case t : ParikhTheory => {
            println()
            println(t)
            println(t.predicates)
            for ((aut, n) <- t.monoidMapPlugin.materialisedAutomata.zipWithIndex) {
              println()
              println("Aut " + n)
              println(aut)
            }
            println()
            println(t.monoidMapPlugin.productFingerprintToId.toSeq.sortBy(_._2) mkString "\n")
          }
        }

        verifyProof3(p)
*/

        Unsat
      }
      case ProverStatus.OutOfMemory => OutOfMemory
      case otherStatus =>
        throw new Exception(s"unexpected solver status: $otherStatus")
    }
  }

/*
  private def verifyProof1(p: SimpleAPI) : Unit = {
    println("Verifying certificate ...")

    import p._
    import IExpression._

    def sym(n : String) : ConstantTerm =
      order.orderedConstants.find(c => c.name == n).get

    val isol = (
sym("R107") === 2 &
sym("R123") === 3 &
sym("R117") === 3 &
sym("R91") === 0 &
sym("R93") === 1 &
sym("R95") === 2 &
sym("R103") === 1 &
sym("R115") === 1 &
sym("R137") === 3 &
sym("R0") === 2 &
sym("R94") === 1 &
sym("R136") === 1 &
sym("R97") === 2 &
sym("R122") === 1 &
sym("R116") === 1 &
sym("R120") === 1 &
sym("R139") === 3 &
sym("R112") === 0 &
sym("R6") === 0 &
sym("R118") === 1 &
sym("R134") === 1 &
sym("R98") === 0 &
sym("R99") === 1 &
sym("R124") === 1 &
sym("R125") === 3 &
sym("R126") === 1 &
sym("R127") === 3 &
sym("R101") === 1 &
sym("R104") === 0 &
sym("R128") === 1 &
sym("R106") === 1 &
sym("R2") === 1 &
sym("R4") === 1 &
sym("R138") === 1 &
sym("R114") === 0 &
sym("R131") === 3 &
sym("R119") === 3 &
sym("R96") === 1 &
sym("R7") === 0 &
sym("R102") === 0 &
sym("R110") === 1 &
sym("R113") === 1 &
sym("R130") === 1 &
sym("R3") === 1 &
sym("R108") === 1 &
sym("R109") === 2 &
sym("R135") === 3 &
sym("R129") === 3 &
sym("R100") === 0 &
sym("R121") === 3 &
sym("R1") === 3 &
sym("R111") === 2 &
sym("R92") === 1 &
sym("R133") === 3 &
sym("R105") === 1 &
sym("R132") === 1
    )

    println("Solution: " + isol)

    val sol = asConjunction(isol)

    def verify(cert : Certificate,
               formulas : Conjunction) : Unit = cert match {
      case BranchInferenceCertificate(Seq(inf1, inf2, infs @ _*), child, order) => {
        verify(BranchInferenceCertificate(List(inf1), 
                                          BranchInferenceCertificate(List(inf2) ++ infs,
                                                                     child, order), order),
               formulas)
      }
      case cert => {
        val reduce = ReduceWithConjunction(sol, cert.order)
        val basesat = !reduce(formulas).isFalse

        var stillsat = false
        for ((subCert, newFors) <- cert.subCertificates zip cert.localProvidedFormulas) {
          val order =
            subCert.order
          val compFor =
            Conjunction.conj(List(formulas) ++ newFors.map(_.toConj), order)
          val reduce =
            ReduceWithConjunction(sol, order)
          if (!reduce(compFor).isFalse) {
            stillsat = true
          }
          verify(subCert, compFor)
        }

        if (basesat && !stillsat) {
          println()
          println("Lost solution:")
          println(cert)
          println()
          println("Assumed formulas:")
          println(cert.assumedFormulas)
          println()
          println("Provided formulas:")
          for (f <- cert.localProvidedFormulas)
            println(f)
        }
      }
    }

    val cert = p.getCertificate
    verify(cert, Conjunction.conj(cert.assumedFormulas.map(_.toConj), order))
  }

  private def verifyProof2(p: SimpleAPI) : Unit = {
    println("Verifying certificate ...")

    import IExpression._

    def sym(n : String) : ConstantTerm =
      p.order.orderedConstants.find(c => c.name == n).get

    val isol = (
sym("R107") === 2 &
sym("R123") === 3 &
sym("R117") === 3 &
sym("R91") === 0 &
sym("R93") === 1 &
sym("R95") === 2 &
sym("R103") === 1 &
sym("R115") === 1 &
sym("R137") === 3 &
sym("R0") === 2 &
sym("R94") === 1 &
sym("R136") === 1 &
sym("R97") === 2 &
sym("R122") === 1 &
sym("R116") === 1 &
sym("R120") === 1 &
sym("R139") === 3 &
sym("R112") === 0 &
sym("R6") === 0 &
sym("R118") === 1 &
sym("R134") === 1 &
sym("R98") === 0 &
sym("R99") === 1 &
sym("R124") === 1 &
sym("R125") === 3 &
sym("R126") === 1 &
sym("R127") === 3 &
sym("R101") === 1 &
sym("R104") === 0 &
sym("R128") === 1 &
sym("R106") === 1 &
sym("R2") === 1 &
sym("R4") === 1 &
sym("R138") === 1 &
sym("R114") === 0 &
sym("R131") === 3 &
sym("R119") === 3 &
sym("R96") === 1 &
sym("R7") === 0 &
sym("R102") === 0 &
sym("R110") === 1 &
sym("R113") === 1 &
sym("R130") === 1 &
sym("R3") === 1 &
sym("R108") === 1 &
sym("R109") === 2 &
sym("R135") === 3 &
sym("R129") === 3 &
sym("R100") === 0 &
sym("R121") === 3 &
sym("R1") === 3 &
sym("R111") === 2 &
sym("R92") === 1 &
sym("R133") === 3 &
sym("R105") === 1 &
sym("R132") === 1
    )

    println("Solution: " + isol)

    val sol = p.asConjunction(isol)

    val q = SimpleAPI.spawn

    q.addConstantsRaw(p.order sort p.order.orderedConstants)
    q.addTheories(p.theories)
    q.addAssertion(sol)

    assert(q.??? == ProverStatus.Sat, "Solution not feasible")

    val cert = p.getCertificate
    val initialFor = Conjunction.conj(cert.assumedFormulas.map(_.toConj), p.order)

    q.addAssertion(initialFor)

    assert(q.??? == ProverStatus.Sat, "Initial assumed formulas not sat")

    def verify(cert : Certificate) : Unit = cert match {
      case BranchInferenceCertificate(Seq(inf1, inf2, infs @ _*), child, order) => {
        verify(BranchInferenceCertificate(List(inf1), 
                                          BranchInferenceCertificate(List(inf2) ++ infs,
                                                                     child, order), order))
      }
      case cert => {
        var stillsat = false
        for ((subCert, newFors) <- cert.subCertificates zip cert.localProvidedFormulas)
          q.scope {
            q.addConstantsRaw(subCert.order sort cert.localBoundConstants)
            for (f <- newFors)
              q.addAssertion(f.toConj)
            println("verifying proof step ...")
            if (q.??? == ProverStatus.Sat) {
              stillsat = true
              verify(subCert)
            }
          }

        if (!stillsat) {
          println()
          println("Lost solution:")
          println(cert)
          println()
          println("Assumed formulas:")
          println(cert.assumedFormulas)
          println()
          println("Provided formulas:")
          for (f <- cert.localProvidedFormulas)
            println(f)
        }
      }
    }

    verify(cert)

  }

  private def verifyProof3(p: SimpleAPI) : Unit = {
    println("Verifying certificate ...")

    import IExpression._

    def sym(n : String) : ConstantTerm =
      p.order.orderedConstants.find(c => c.name == n).get

    val isol = (
sym("R107") === 2 &
sym("R123") === 3 &
sym("R117") === 3 &
sym("R91") === 0 &
sym("R93") === 1 &
sym("R95") === 2 &
sym("R103") === 1 &
sym("R115") === 1 &
sym("R137") === 3 &
sym("R0") === 2 &
sym("R94") === 1 &
sym("R136") === 1 &
sym("R97") === 2 &
sym("R122") === 1 &
sym("R116") === 1 &
sym("R120") === 1 &
sym("R139") === 3 &
sym("R112") === 0 &
sym("R6") === 0 &
sym("R118") === 1 &
sym("R134") === 1 &
sym("R98") === 0 &
sym("R99") === 1 &
sym("R124") === 1 &
sym("R125") === 3 &
sym("R126") === 1 &
sym("R127") === 3 &
sym("R101") === 1 &
sym("R104") === 0 &
sym("R128") === 1 &
sym("R106") === 1 &
sym("R2") === 1 &
sym("R4") === 1 &
sym("R138") === 1 &
sym("R114") === 0 &
sym("R131") === 3 &
sym("R119") === 3 &
sym("R96") === 1 &
sym("R7") === 0 &
sym("R102") === 0 &
sym("R110") === 1 &
sym("R113") === 1 &
sym("R130") === 1 &
sym("R3") === 1 &
sym("R108") === 1 &
sym("R109") === 2 &
sym("R135") === 3 &
sym("R129") === 3 &
sym("R100") === 0 &
sym("R121") === 3 &
sym("R1") === 3 &
sym("R111") === 2 &
sym("R92") === 1 &
sym("R133") === 3 &
sym("R105") === 1 &
sym("R132") === 1
    )

    println("Solution: " + isol)

    val sol = p.asConjunction(isol)

    val q = SimpleAPI.spawn

    q.addConstantsRaw(p.order sort p.order.orderedConstants)
    q.addTheories(p.theories)
    q.addAssertion(sol)

    assert(q.??? == ProverStatus.Sat, "Solution not feasible")

    val cert = p.getCertificate

    q.scope {
      val initialFor = Conjunction.conj(cert.assumedFormulas.map(_.toConj), p.order)
      q.addAssertion(initialFor)
      assert(q.??? == ProverStatus.Sat, "Initial assumed formulas not sat")
    }

    def verify(cert : Certificate,
               formulas : Set[CertFormula]) : Unit = cert match {
      case BranchInferenceCertificate(Seq(inf1 : TheoryAxiomInference,
                                          inf2 : GroundInstInference,
                                          inf3,
                                          infs @ _*), child, order) => {
        verify(BranchInferenceCertificate(List(inf1, inf2),
                                          BranchInferenceCertificate(List(inf3) ++ infs,
                                                                     child, order), order),
               formulas)
      }
      case BranchInferenceCertificate(Seq(inf1, inf2, infs @ _*), child, order)
          if !(inf1.isInstanceOf[TheoryAxiomInference] &&
                 inf2.isInstanceOf[GroundInstInference]) => {
        verify(BranchInferenceCertificate(List(inf1), 
                                          BranchInferenceCertificate(List(inf2) ++ infs,
                                                                     child, order), order),
               formulas)
      }
      case cert => {
        var stillsat = false
        println("considering proof step: " + cert.getClass)
        for ((subCert, newFors) <- cert.subCertificates zip cert.localProvidedFormulas)
          q.scope {
            println("verifying that solution is still present ... ")

            q.addConstantsRaw(subCert.order sort cert.localBoundConstants)

            val remFormulas =
              formulas -- (cert.localAssumedFormulas -- subCert.assumedFormulas)
            val allFormulas =
              remFormulas ++ newFors

            println(allFormulas mkString ", ")

            val status = q.scope {
              for (f <- allFormulas)
                q.addAssertion(f.toConj)
              q.???
            }
            if (status == ProverStatus.Sat) {
              stillsat = true
              verify(subCert, allFormulas)
            }
          }

        if (!stillsat) {
          println()
          println("Lost solution:")
          println(cert)
          println()
          println("Assumed formulas:")
          println(cert.assumedFormulas)
          println()
          println("Provided formulas:")
          for (f <- cert.localProvidedFormulas)
            println(f)
        }
      }
    }

    verify(cert, cert.assumedFormulas)

  }
*/

  override def solveSatisfy(instance: Instance): Try[SatisfactionResult] =
    trace("solveSatisfy result") {
      arguments.withProver { p =>
        try {
          val counterToConstants = prepareSolver(p, instance)
          checkSolutions(p, instance)(counterToConstants)
        } catch {
          case _: OutOfMemoryError =>
            p.stop
            OutOfMemory
        }
      }
    }
}
