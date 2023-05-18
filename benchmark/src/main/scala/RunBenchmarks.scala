package uuverifiers
import fastparse.Parsed
import uuverifiers.catra.SatisfactionResult

import java.util.Calendar
import scala.util.{Failure, Random, Success, Try}
import scala.collection.parallel.CollectionConverters._

object RunBenchmarks extends App {
  import catra.SolveRegisterAutomata.measureTime

  private val baseConf = Array("solve-satisfy", "--timeout", "120000")
  private val nrMaterialiseEager = 500
  private val nrMaterialiseLazy = 1
  private val configurations = Map(
    "lazy-norestart" -> Array("--backend", "lazy", "--no-restarts"),
    "nuxmv" -> Array("--backend", "nuxmv"),
    //"baseline" -> Array("--backend", "baseline", "--timeout", "30000"), // We know baseline doesn't improve beyond 30s
    "lazy-regular" -> Array("--backend", "lazy"),
    "lazy-no-clauselearning" -> Array(
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

  {
    val runtime = Runtime.getRuntime
    print(
      s"INFO ${Calendar.getInstance().getTime} JVM version: ${System.getProperty("java.version")}"
    )
    println(s" Heap size: total: ${runtime.totalMemory()}B, max: ${runtime
      .maxMemory()}B, free: ${runtime.freeMemory()}B")
  }

  private val (_, runtime) = measureTime {
    val results = experiments.par
      .map {
        case (instanceName, instance, config, configName) =>
          val resultAndTime =
            measureTime(config.getBackend().solveSatisfy(instance))
          (instanceName, configName, resultAndTime)
      }
      .iterator
      .toSeq
      .groupBy(_._1)
      .view
      .mapValues(_.map(s => (s._2, s._3)))

    println(s"CONFIGS ${configNames.mkString("\t")}")
    for ((instance, rs) <- results) {
      val rsMap = rs.toMap
      println(
        s"RESULT $instance\t${configNames.map(c => fmtResult(rsMap(c))).mkString("\t")}"
      )
    }
  }

  println(
    s"INFO ${Calendar.getInstance().getTime} Executed ${experiments.length} experiments with ${configurations.size} configurations and ${instances.length} instances in $runtime."
  )

}
