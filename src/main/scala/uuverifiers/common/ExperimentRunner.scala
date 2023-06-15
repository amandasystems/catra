package uuverifiers.common

import uuverifiers.catra.{CommandLineOptions, Instance, SatisfactionResult}
import uuverifiers.catra.SolveRegisterAutomata.measureTime

import java.util.concurrent.{ExecutorService, Executors}
import scala.collection.MapView
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration.Duration
import scala.util.Try

sealed class ExperimentRunner(
    experiments: Seq[(String, Instance, CommandLineOptions, String)],
    nrWorkers: Int
) {

  // Default: use half the CPUs
  private val threadPool: ExecutorService =
    Executors.newFixedThreadPool(nrWorkers)

  implicit private val ec: ExecutionContext = new ExecutionContext {

    def execute(runnable: Runnable): Unit = {
      threadPool.submit(runnable)
    }

    def reportFailure(t: Throwable): Unit = {
      println(s"WARN: error running experiment: $t")
    }

  }

  private val tasks =
    for ((instanceName, instance, config, configName) <- experiments)
      yield Future {
        val resultAndTime =
          measureTime(config.getBackend.solveSatisfy(instance))
        (instanceName, configName, resultAndTime)
      }
  def results(
      deadline: Duration
  ): Try[MapView[String, Seq[(String, (Try[SatisfactionResult], Double))]]] =
    Try(
      Await
        .result(Future.sequence(tasks), deadline)
        .groupBy(_._1)
        .view
        .mapValues(_.map(s => (s._2, s._3)))
    )

  def stop(): Unit = {
    threadPool.shutdown()
  }
}
