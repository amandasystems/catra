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

case object ChoosePrincess extends BackendSelection {
  override def toString: String = "princess"
}
case object ChooseNuxmv extends BackendSelection {
  override def toString: String = "nuxmv"
}

case object ChooseVerma extends BackendSelection {
  override def toString: String = "verma"
}

sealed trait RunMode
case object SolveSatisfy extends RunMode
case object FindImage extends RunMode

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
    dumpEquationDir: Option[File]
) {

  def getBackend(): Backend = backend match {
    case ChoosePrincess => new PrincessBackend(this)
    case ChooseNuxmv    => new NUXMVBackend(this)
    case ChooseVerma    => new VermaBackend(this)
  }

  def runWithTimeout(p: SimpleAPI)(block: => SatisfactionResult): Try[SatisfactionResult] =
    try {
      timeout_ms match {
        case Some(timeout_ms) =>
          p.withTimeout(timeout_ms) {
            ap.util.Timeout.withTimeoutMillis(timeout_ms) {
              Success(block)
            } {
              Success(Timeout(timeout_ms))
            }
          }
        case None => Success(block)
      }
    } catch {
      case SimpleAPI.TimeoutException =>
        p.stop
        Success(Timeout(timeout_ms.getOrElse(0)))
      case ap.util.Timeout(_) =>
        p.stop
        Success(Timeout(timeout_ms.getOrElse(0)))
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
  private var backend: BackendSelection = ChoosePrincess
  private var noCheckTermSat = false
  private var noCheckIntermediateSat = false
  private var noEliminateQuantifiers = false
  private var dumpEquationDir: Option[File] = None

  private val usage =
    s"""
    Usage: <subcommand> <options> <files or directories>

    Available subcommands:
      solve-satisfy -- look for a satisfying solution
      find-image -- generate the full Parikh image in Presburger format
    
    Available options (🐌 = likely to negatively impact performance):
      --trace -- generate a trace of the computation into trace.tex,
                  plus various .dot files. (default = $trace) 🐌
      --print-decisions -- log partial decisions. Less verbose trace.
      --timeout milliseconds -- set the timeout in ms (default = $timeout_ms)
      --dump-smt <directory> -- dump SMT commands into this directory
                                 (default = $dumpSMTDir) 🐌
      --backend <backend> -- choose which back-end to use.
                             Available options are: nuxmv, princess, verma.
                             Default: $backend.
      --dump-graphviz <directory> -- dump automata encountered while solving
                            into this directory. Default is disabled.

    For specific back-ends:

      Verma:
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
                        penalises satisfiable instances. Default: $noEliminateQuantifiers
      Note: for maximally lazy computation (and to maximally prioritise satisifiable
                        instances), set all these to false.

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
            matchingFiles = matchingFiles appended file
              .toAbsolutePath()
              .toString()
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

  private def expandFileNameOrDirectoryOrGlob(
      filePattern: String
  ): Seq[String] = {
    val expandedHomePath =
      Paths.get(filePattern.replaceFirst("^~", System.getProperty("user.home")))

    expandedHomePath.toFile() match {
      case f if f.isDirectory() => enumerateDirectory(expandedHomePath)
      case f if f.exists()      => Seq(expandedHomePath.toString())
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
      case "--no-eliminate-quantifiers" :: tail =>
        noEliminateQuantifiers = true
        parseFilesAndFlags(tail)
      case "--backend" :: "princess" :: tail =>
        parseFilesAndFlags(tail)
      case "--backend" :: "nuxmv" :: tail =>
        backend = ChooseNuxmv
        parseFilesAndFlags(tail)
      case "--backend" :: "verma" :: tail =>
        backend = ChooseVerma
        parseFilesAndFlags(tail)
      case "--dump-equations" :: directory :: tail =>
        dumpEquationDir = Some(new File(directory))
        parseFilesAndFlags(tail)
      case "--backend" :: other :: _ =>
        throw new IllegalArgumentException(s"Unknown backend: $other!")
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
      dumpEquationDir = dumpEquationDir
    )
  }
}
