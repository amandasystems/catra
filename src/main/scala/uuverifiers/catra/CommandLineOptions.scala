package uuverifiers.catra
import scala.util.Try
import java.nio.file.FileSystems
import java.nio.file.SimpleFileVisitor
import java.nio.file.Files
import java.nio.file.Paths
import java.nio.file.Path
import java.nio.file.FileVisitResult
import java.nio.file.attribute.BasicFileAttributes
import java.io.{File, IOException}
import ap.SimpleAPI

import scala.annotation.tailrec
import scala.util.Success
import scala.util.Failure

sealed trait BackendSelection

object BackendSelection {
  def apply(name: String): BackendSelection =
    Seq(ChooseLazy, ChooseNuxmv, ChooseBaseline)
      .find(_.toString() == name)
      .getOrElse {
        throw new IllegalArgumentException(s"Unknown backend: $name!")
      }
}

case object ChooseLazy extends BackendSelection {
  override def toString: String = "lazy"
}
case object ChooseNuxmv extends BackendSelection {
  override def toString: String = "nuxmv"
}

case object ChooseBaseline extends BackendSelection {
  override def toString: String = "baseline"
}

sealed trait RunMode
case object SolveSatisfy extends RunMode
case object FindImage extends RunMode
case object DebugUnsat extends RunMode

sealed case class CommandLineOptions(
    inputFiles: Seq[String],
    timeout_ms: Option[Long],
    dumpSMTDir: Option[File],
    dumpGraphvizDir: Option[File],
    trace: Boolean,
    printDecisions: Boolean,
    runMode: RunMode,
    backend: BackendSelection,
    checkTermSat: Boolean,
    checkIntermediateSat: Boolean,
    eliminateQuantifiers: Boolean,
    dumpEquationDir: Option[File],
    nrUnknownToMaterialiseProduct: Int,
    enableClauseLearning: Boolean,
    enableRestarts: Boolean,
    restartTimeoutFactor: Long,
    crossValidate: Boolean,
    randomSeed: Int,
    printProof: Boolean
) {
  def withRandomSeed(newSeed: Int): CommandLineOptions =
    copy(randomSeed = newSeed)

  def withRestartTimeoutFactor(newValue: Long): CommandLineOptions =
    copy(restartTimeoutFactor = newValue)

  def withProver[R <: Result](f: SimpleAPI => R): Try[R] =
    dumpSMTDir match {
      case None =>
        SimpleAPI.withProver(
          randomSeed = Some(randomSeed)
          //logging = Set(ap.parameters.Param.LOG_LEMMAS)
        )(
          p => runWithTimeout(p)(f(p))
        )
      case Some(dumpDir) =>
        SimpleAPI.withProver(
          dumpSMT = true,
          dumpDirectory = dumpDir,
          randomSeed = Some(randomSeed)
        )(
          p => runWithTimeout(p)(f(p))
        )
    }

  def getBackend(): Backend = backend match {
    case ChooseLazy     => new LazyBackend(this)
    case ChooseNuxmv    => new NUXMVBackend(this)
    case ChooseBaseline => new BaselineBackend(this)
  }

  def runWithTimeout[R <: Result](
      p: SimpleAPI
  )(block: => R): Try[R] =
    try {
      timeout_ms match {
        case Some(timeout_ms) =>
          p.withTimeout(timeout_ms) {
            ap.util.Timeout.withTimeoutMillis(timeout_ms) {
              Success(block)
            } {
              Success(Timeout(timeout_ms).asInstanceOf[R])
            }
          }
        case None => Success(block)
      }
    } catch {
      case SimpleAPI.TimeoutException =>
        p.stop
        Success(Timeout(timeout_ms.getOrElse(0)).asInstanceOf[R])
      case ap.util.Timeout(_) =>
        p.stop
        Success(Timeout(timeout_ms.getOrElse(0)).asInstanceOf[R])
      case e: Throwable => Failure(e)
    }
}

object CommandLineOptions {
  private val fileSystem = FileSystems.getDefault()
  private val fileExtension = ".par"
  var runMode: RunMode = SolveSatisfy

  /// Option fields
  private var timeout_ms: Option[Long] = None
  private var trace = false
  private var printDecisions = false
  private var inputFiles: Seq[String] = Seq()
  private var dumpSMTDir: Option[File] = None
  private var dumpGraphvizDir: Option[File] = None
  private var backend: BackendSelection = ChooseLazy
  private var noCheckTermSat = false
  private var noCheckIntermediateSat = false
  private var noEliminateQuantifiers = false
  private var dumpEquationDir: Option[File] = None
  private var nrUnknownToStartMaterialiseProduct = 2 // FIXME: increase to 6.
  private var enableClauseLearning: Boolean = true
  private var enableRestarts = true
  private var restartTimeoutFactor = 500L
  private var crossValidate = false
  private var randomSeed = 1234567
  private var printProof = false

  private val usage =
    s"""
    Usage: <subcommand> <options> <files or directories>

    Available subcommands:
      solve-satisfy -- look for a satisfying solution
      find-image -- generate the full Parikh image in Presburger format
      debug-unsat -- diagnose (an) incorrect unsat result(s)

    Available options (🐌 = likely to negatively impact performance):
      --trace -- generate a trace of the computation into trace.tex,
                  plus various .dot files. (default = $trace) 🐌
      --print-decisions -- log partial decisions. Less verbose trace.
      --timeout milliseconds -- set the timeout in ms (default = $timeout_ms)
      --dump-smt <directory> -- dump SMT commands into this directory
                                 (default = $dumpSMTDir) 🐌
      --backend <backend> -- choose which back-end to use.
                             Available options are: nuxmv, lazy, baseline.
                             Default: $backend.
      --dump-graphviz <directory> -- dump automata encountered while solving
                            into this directory. Default is disabled.

    For specific back-ends:

      Baseline:
      --print-proof     -- compute and generate a proof upon (non-) solution. 
                        May extend runtime. Default: $printProof.
      --dump-equations <directory> -- dump the flow equations of each consecutive
                        product (and all terms) as LaTeX equations into this directory.
      --no-check-term-sat -- Check first if the terms of the product alone are
                        unsatisfiable. This corresponds to over-approximating the
                        Parikh image to the conjunction of the images, but leaves
                        the produced clauses in the solver, allowing it to detect
                        clashes with intermittent products. Penalises satisfiable
                        instances. Default: $noCheckTermSat. Quantifier Elimination
                        suggested.
      --no-check-intermediate-sat -- Check if each intermediate product is
                        satisifiable before continuing. Penalises satisifiable
                        instances. Default: $noCheckIntermediateSat. Quantifier
                        elimination suggested.
      --no-eliminate-quantifiers -- Perform quantifier elimination before adding
                        the clauses representing the Parikh image to Princess.
                        This takes time, in particular for large clauses, and
                        penalises satisfiable instances. On the other hand it
                        accelerates incremental querying. Default: $noEliminateQuantifiers
      Note: for maximally lazy computation (and to maximally prioritise satisifiable
                        instances), set all these to false.
                        
      Lazy
      --nr-unknown-to-start-materialise -- Start materialising products when the most
         well-known automaton has this many unknown transitions.
         0 means be as lazy as possible. For more eagerness, set a ludicrously large number.
                        Default: $nrUnknownToStartMaterialiseProduct.
      --no-clause-learning -- What it says on the tin.
      --no-restarts -- disable periodical restarts. Experimentally better for SAT.
      --restart-timeout-factor -- The level of willingness to try before restarting.
                       Default: $restartTimeoutFactor.
         

    Environment variables:
      CATRA_TRACE -- if set to "true", enable very very verbose logging 🐌
  """

  private def enumerateDirectory(dir: Path): Seq[String] = {
    val pathMatcher = fileSystem.getPathMatcher(s"glob:**$fileExtension")

    var matchingFiles: Seq[String] = Seq()

    Files.walkFileTree(
      dir,
      new SimpleFileVisitor[Path] {
        import FileVisitResult.CONTINUE
        override def visitFile(
            file: Path,
            attrs: BasicFileAttributes
        ): FileVisitResult = {
          if (pathMatcher.matches(file)) {
            matchingFiles = matchingFiles appended relativeToHere(file.toFile)
          }
          CONTINUE
        }
        override def visitFileFailed(
            file: Path,
            exc: IOException
        ): FileVisitResult = CONTINUE
      }
    )
    matchingFiles
  }

  private def relativeToHere(f: File): String = {
    val here = Paths.get(new File(".").getCanonicalPath())
    (here relativize Paths.get(f.getCanonicalPath())).toString
  }

  private def expandFileNameOrDirectoryOrGlob(
      filePattern: String
  ): Seq[String] = {
    val expandedHomePath =
      Paths.get(filePattern.replaceFirst("^~", System.getProperty("user.home")))

    expandedHomePath.toFile() match {
      case f if f.isDirectory() => enumerateDirectory(expandedHomePath)
      case f if f.exists()      => Seq(relativeToHere(f))
      case f =>
        Console.err.println(s"W: file $f does not exist; skipping!")
        Seq()
    }
  }

  @tailrec
  def parseFilesAndFlags(args: List[String]): Unit = {
    args match {
      case Nil                       =>
      case "--" :: tail              => parseFilesAndFlags(tail)
      case "--help" :: _ | "-h" :: _ => throw new Exception(usage)
      case "--print-decisions" :: tail =>
        printDecisions = true
        parseFilesAndFlags(tail)
      case "--trace" :: tail =>
        trace = true
        parseFilesAndFlags(tail)
      case "--timeout" :: milliseconds :: tail =>
        timeout_ms = Some(milliseconds.toLong)
        parseFilesAndFlags(tail)
      case "--dump-smt" :: directory :: tail =>
        dumpSMTDir = Some(new File(directory))
        parseFilesAndFlags(tail)
      case "--dump-graphviz" :: directory :: tail =>
        dumpGraphvizDir = Some(new File(directory))
        parseFilesAndFlags(tail)
      case "--no-check-term-sat" :: tail =>
        noCheckTermSat = true
        parseFilesAndFlags(tail)
      case "--no-check-intermediate-sat" :: tail =>
        noCheckIntermediateSat = true
        parseFilesAndFlags(tail)
      case "--no-clause-learning" :: tail =>
        enableClauseLearning = false
        parseFilesAndFlags(tail)
      case "--no-restarts" :: tail =>
        enableRestarts = false
        parseFilesAndFlags(tail)
      case "--no-eliminate-quantifiers" :: tail =>
        noEliminateQuantifiers = true
        parseFilesAndFlags(tail)
      case "--nr-unknown-to-start-materialise" :: someNr :: tail =>
        nrUnknownToStartMaterialiseProduct = someNr.toInt
        parseFilesAndFlags(tail)
      case "--backend" :: someBackendName :: tail =>
        backend = BackendSelection(someBackendName)
        parseFilesAndFlags(tail)
      case "--dump-equations" :: directory :: tail =>
        dumpEquationDir = Some(new File(directory))
        parseFilesAndFlags(tail)
      case "--cross-validate" :: tail =>
        crossValidate = true
        parseFilesAndFlags(tail)
      case "--restart-timeout-factor" :: someFactor :: tail =>
        restartTimeoutFactor = someFactor.toLong
        parseFilesAndFlags(tail)
      case "--print-proof" :: tail =>
        printProof = true
        parseFilesAndFlags(tail)
      case option :: _ if option.matches("--.*") =>
        throw new IllegalArgumentException(s"unknown option: $option!")
      case other :: tail =>
        inputFiles ++= expandFileNameOrDirectoryOrGlob(other)
        parseFilesAndFlags(tail)
    }
  }

  @tailrec
  def parseMode(args: List[String]): Unit = args match {
    case Nil                       => throw new Exception("Error: No mode specified! \n\n" + usage)
    case "--" :: tail              => parseMode(tail)
    case "--help" :: _ | "-h" :: _ => throw new Exception(usage)
    case "solve-satisfy" :: rest   => parseFilesAndFlags(rest)
    case "find-image" :: rest =>
      runMode = FindImage
      parseFilesAndFlags(rest)
    case "debug-unsat" :: rest =>
      runMode = DebugUnsat
      parseFilesAndFlags(rest)
    case other :: _ =>
      throw new Exception(s"Error: Invalid mode `$other`!\n\n" + usage)
  }

  def parse(args: Array[String]): Try[CommandLineOptions] = Try {

    parseMode(args.toList)

    CommandLineOptions(
      inputFiles = util.Random.shuffle(inputFiles),
      timeout_ms = timeout_ms,
      trace = trace,
      printDecisions = printDecisions,
      dumpSMTDir = dumpSMTDir,
      dumpGraphvizDir = dumpGraphvizDir,
      runMode = runMode,
      backend = backend,
      checkTermSat = !noCheckTermSat,
      checkIntermediateSat = !noCheckIntermediateSat,
      eliminateQuantifiers = !noEliminateQuantifiers,
      dumpEquationDir = dumpEquationDir,
      nrUnknownToMaterialiseProduct = nrUnknownToStartMaterialiseProduct,
      enableClauseLearning = enableClauseLearning,
      enableRestarts = enableRestarts,
      restartTimeoutFactor = restartTimeoutFactor,
      crossValidate = crossValidate,
      randomSeed = randomSeed,
      printProof = printProof
    )
  }
}
