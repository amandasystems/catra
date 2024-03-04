package uuverifiers.common

import uuverifiers.catra.{CommandLineOptions, Instance, SatisfactionResult}
import uuverifiers.catra.SolveRegisterAutomata.measureTime

import java.util.concurrent.{ExecutorService, Executors}
import scala.collection.MapView
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration.Duration
import scala.util.Try
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException
import scala.util.Success
import uuverifiers.catra.Timeout

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
      yield {
        val myDeadline =
          Duration(config.timeout_ms.get + 1000, TimeUnit.MILLISECONDS)
        val resultsFut = Future {
          val resultAndTime =
            measureTime(config.getBackend().solveSatisfy(instance))
          (instanceName, configName, resultAndTime)
        }

        val futWithDeadline = Future {
          try {
            Await.result(resultsFut, myDeadline)
          } catch {
            case _: TimeoutException => {
              val syntheticTimeoutResult =
                Success(Timeout(config.timeout_ms.get))

              val syntheticTime = (config.timeout_ms.get / 1000).toDouble

              (
                instanceName,
                configName,
                (syntheticTimeoutResult, syntheticTime)
              )
            }
          }
        }

        futWithDeadline
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
