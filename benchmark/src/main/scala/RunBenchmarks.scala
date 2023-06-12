package uuverifiers
import fastparse.Parsed
import uuverifiers.catra.SatisfactionResult

import java.util.Calendar
import scala.concurrent.duration.Duration
import scala.concurrent.{TimeoutException, duration}
import scala.util.{Failure, Random, Success, Try}
import uuverifiers.common.ExperimentRunner

object RunBenchmarks extends App {
  import catra.SolveRegisterAutomata.measureTime
  private val regularTimeout = 20000
  private val baseConf =
    Array("solve-satisfy", "--timeout", regularTimeout.toString)
  private val nrMaterialiseEager = 500
  private val nrMaterialiseLazy = 1
  private val configurations = Map(
//    "lazy-norestart" -> Array("--backend", "lazy", "--no-restarts"),
    "nuxmv" -> Array("--backend", "nuxmv"),
//    "baseline" -> Array("--backend", "baseline", "--timeout", "30000"), // We know baseline doesn't improve beyond 30s
    "lazy" -> Array("--backend", "lazy")
//    "lazy-no-clauselearning" -> Array(
//      "--backend",
//      "lazy",
//      "--no-restarts",
//      "--no-clause-learning"
//    ),
//    s"lazy-eager-$nrMaterialiseEager" -> Array(
//      "--backend",
//      "lazy",
//      "--nr-unknown-to-start-materialise",
//      nrMaterialiseEager.toString
//    ),
//    s"lazy-lazy-$nrMaterialiseLazy" -> Array(
//      "--backend",
//      "lazy",
//      "--nr-unknown-to-start-materialise",
//      nrMaterialiseLazy.toString
//    )
  ).view
    .mapValues(
      c => catra.CommandLineOptions.parse(baseConf ++ c).get
    )
    .toMap

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

  private val configNames = configurations.keys.toSeq.sorted

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
        configName => (file, instance, configurations(configName), configName)
      )
  }.toSeq)

  private val runtime = Runtime.getRuntime
  private val nrWorkers = runtime.availableProcessors / 2

  print(
    s"INFO ${Calendar.getInstance().getTime} JVM version: ${System.getProperty("java.version")}"
  )
  println(
    s" Heap size: total: ${runtime.totalMemory()}B, max: ${runtime
      .maxMemory()}B, free: ${runtime.freeMemory()}B, nr cores: ${runtime.availableProcessors}, using: $nrWorkers"
  )

  private val (_, totalTimeSpent) = measureTime {
    val runner = new ExperimentRunner(experiments, nrWorkers)

    println(s"CONFIGS ${configNames.mkString("\t")}")
    configurations.foreachEntry {
      case (name, config) =>
        println(s"CONFIG $name IS $config")
    }
    println(s"TIMEOUT $regularTimeout")

    val safetyMargin = 1000 * experiments.length
    val maxTimeout = Duration(
      (experiments.length * regularTimeout) + safetyMargin,
      duration.MILLISECONDS
    )

    println(s"HARD TIMEOUT $maxTimeout FOR ALL")

    runner.results(maxTimeout) match {
      case Failure(_: TimeoutException) =>
        println("ERR hard timeout, some experiment is misbehaving!")
      case Failure(e) => println(s"ERR unknown error running experiments: $e")
      case Success(outcomes) =>
        for ((instance, rs) <- outcomes) {
          val rsMap = rs.toMap
          println(
            s"RESULT $instance\t${configNames.map(c => fmtResult(rsMap(c))).mkString("\t")}"
          )
        }
    }
    runner.stop()
  }

  println(
    s"INFO ${Calendar.getInstance().getTime} Executed ${experiments.length} experiments with ${configurations.size} configurations and ${instances.length} instances in $totalTimeSpent."
  )

}
