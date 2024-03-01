package uuverifiers
import fastparse.Parsed
import uuverifiers.catra.SatisfactionResult
import uuverifiers.common.ExperimentRunner

import java.util.Calendar
import scala.concurrent.duration.Duration
import scala.concurrent.{TimeoutException, duration}
import scala.util.{Failure, Random, Success, Try}

object RunBenchmarks extends App {
  import catra.SolveRegisterAutomata.measureTime
  private val timeout =
    sys.env.getOrElse("CATRA_TIMEOUT", "30000").toInt
  private val nrMaterialiseEager = 200
  private val nrMaterialiseLazy = 1
  private val baseConfigurations = Map(
    "nuxmv" -> Array("--backend", "nuxmv"),
    "baseline" -> Array("--backend", "baseline"),
    "lazy" -> Array("--backend", "lazy"),
    "lazy-no-clauselearning" -> Array(
      "--backend",
      "lazy",
      "--no-clause-learning"
    ),
    "lazy-no-clauselearning-no-restarts" -> Array(
      "--backend",
      "lazy",
      "--no-restarts",
      "--no-clause-learning"
    ),
    s"lazy-eager-$nrMaterialiseEager" -> Array(
      "--backend",
      "lazy",
      "--nr-unknown-to-start-materialise",
      nrMaterialiseEager.toString
    ),
    s"lazy-lazy-$nrMaterialiseLazy" -> Array(
      "--backend",
      "lazy",
      "--nr-unknown-to-start-materialise",
      nrMaterialiseLazy.toString
    )
  ).view
    .mapValues(
      c =>
        catra.CommandLineOptions
          .parse(
            Array("solve-satisfy", "--timeout", timeout.toString) ++ c
          )
          .get
    )
    .toMap

  private val selectConfigurations = sys.env
    .getOrElse("CATRA_CONFIGS", baseConfigurations.keys.mkString(","))
    .split(",")
    .toSet
  private val filteredConfigurations =
    baseConfigurations.view.filterKeys(selectConfigurations.contains).toMap

  private val instanceFiles =
    args.flatMap(catra.CommandLineOptions.expandFileNameOrDirectoryOrGlob)

  private val instances = instanceFiles
    .flatMap(
      f =>
        catra.InputFileParser.parseFile(f) match {
          case Parsed.Success(value, _) => Some(f -> value)
          case _                        => None
        }
    )

  private val configNames = filteredConfigurations.keys.toSeq.sorted

  private def fmtResult(r: (Try[SatisfactionResult], Double)): String = {
    r match {
      case (Failure(_), _)                      => "e"
      case (Success(catra.Sat(_)), runtime)     => s"s$runtime"
      case (Success(catra.Unsat), runtime)      => s"u$runtime"
      case (Success(catra.Timeout(_)), runtime) => s"t$runtime"
      case (Success(catra.OutOfMemory), _)      => "m"
    }
  }

  // Shuffle the experiments to prevent systemic bias between configurations!
  private val experiments = Random.shuffle(instances.flatMap {
    case (file, instance) =>
      configNames.map(
        configName =>
          (file, instance, filteredConfigurations(configName), configName)
      )
  }.toSeq)

  private val runtime = Runtime.getRuntime
  private val nrWorkers = sys.env.getOrElse("CATRA_THREADS", "6").toInt

  print(
    s"INFO ${Calendar.getInstance().getTime} JVM version: ${System.getProperty("java.version")}"
  )
  println(
    s" Heap size: total: ${runtime.totalMemory()}B, max: ${runtime
      .maxMemory()}B, free: ${runtime.freeMemory()}B, nr cores: ${runtime.availableProcessors}, using: $nrWorkers"
  )

  println("INFO: doing warm-up run...")
  catra.CommandLineOptions
    .default()
    .withTimeout(Some(10000))
    .getBackend()
    .solveSatisfy(instances(0)._2)
  println("...warm-up done!")

  private val (exitCode, totalTimeSpent) = measureTime {
    val runner = new ExperimentRunner(experiments, nrWorkers)

    println(s"CONFIGS ${configNames.mkString("\t")}")
    filteredConfigurations.foreachEntry {
      case (name, config) =>
        println(s"CONFIG $name IS $config")
    }
    println(s"TIMEOUT $timeout")

    val safetyMargin = 1000 * experiments.length
    val maxTimeout = Duration(
      (experiments.length * timeout) + safetyMargin,
      duration.MILLISECONDS
    )

    println(s"HARD TIMEOUT $maxTimeout FOR ALL")

    val exitCode = runner.results(maxTimeout) match {
      case Failure(_: TimeoutException) => {
        println("ERR hard timeout, some experiment is misbehaving!")
        1
      }
      case Failure(e) => {
        println(s"ERR unknown error running experiments: $e")
        1
      }
      case Success(outcomes) => {
        for ((instance, rs) <- outcomes) {
          val rsMap = rs.toMap
          println(
            s"RESULT $instance\t${configNames.map(c => fmtResult(rsMap(c))).mkString("\t")}"
          )
        }
        0
      }
    }
    runner.stop()
    exitCode
  }

  println(
    s"INFO ${Calendar.getInstance().getTime} Executed ${experiments.length} experiments with ${filteredConfigurations.size} configurations and ${instances.length} instances in $totalTimeSpent."
  )
  System.exit(exitCode)

}
