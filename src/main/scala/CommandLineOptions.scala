package uuverifiers.parikh_theory
import scala.util.Try
import java.nio.file.FileSystems
import java.nio.file.SimpleFileVisitor
import java.nio.file.Files
import java.nio.file.Paths
import java.nio.file.Path
import java.nio.file.FileVisitResult
import java.nio.file.attribute.BasicFileAttributes
import java.io.{IOException, File}

sealed trait BackendSelection

case object ChoosePrincess extends BackendSelection {
  override def toString: String = "princess"
}
case object ChooseNuxmv extends BackendSelection {
  override def toString: String = "princess"
}

sealed trait RunMode
case object SolveSatisfy extends RunMode
case object FindImage extends RunMode

sealed case class CommandLineOptions(
    inputFiles: Seq[String],
    timeout_ms: Option[Long],
    dumpSMTDir: Option[File],
    trace: Boolean,
    runMode: RunMode,
    backend: BackendSelection
) {
  def getBackend(): Backend = backend match {
    case ChoosePrincess => new PrincessBackend(this)
    case ChooseNuxmv    => new NUXMVBackend(this)
  }
}

object CommandLineOptions {
  private val fileSystem = FileSystems.getDefault()
  private val fileExtension = ".par"
  var runMode: RunMode = SolveSatisfy

  /// Option fields
  private var timeout_ms: Option[Long] = None
  private var trace = false
  private var inputFiles: Seq[String] = Seq()
  private var dumpSMTDir: Option[File] = None
  private var backend: BackendSelection = ChoosePrincess

  private val usage =
    s"""
    Usage: <subcommand> <options> <files or directories>

    Available subcommands:
      solve-satisfy -- look for a satisfying solution
      find-image -- generate the full Parikh image in Presburger format
    
    Available options (🐌 = likely to negatively impact performance):
      --trace -- generate a trace of the computation into trace.tex,
                  plus various .dot files. (default = ${trace}) 🐌
      --timeout milliseconds -- set the timeout in ms (default = ${timeout_ms})
      --dump-smt <directory> -- dump SMT commands into this directory
                                 (default = ${dumpSMTDir}) 🐌
      --backend <backend> -- choose which back-end to use.
                             Available options are: nuxmv, princess.
                             Default: ${backend}.
    Environment variables:
      OSTRICH_TRACE -- if set to "true", enable very very verbose logging 🐌
  """

  private def enumerateDirectory(dir: Path): Seq[String] = {
    val pathMatcher = fileSystem.getPathMatcher(s"glob:**${fileExtension}")

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
            matchingFiles = matchingFiles appended (file
              .toAbsolutePath()
              .toString())
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
      case f => {
        Console.err.println(s"W: file ${f} does not exist; skipping!")
        Seq()
      }
    }
  }

  def parseFilesAndFlags(args: List[String]): Unit = {
    args match {
      case Nil                       =>
      case "--" :: tail              => parseFilesAndFlags(tail)
      case "--help" :: _ | "-h" :: _ => throw new Exception(usage)
      case "--trace" :: tail => {
        trace = true
        parseFilesAndFlags(tail)
      }
      case "--timeout" :: milliseconds :: tail => {
        timeout_ms = Some(milliseconds.toLong)
        parseFilesAndFlags(tail)
      }
      case "--dump-smt" :: directory :: tail => {
        dumpSMTDir = Some(new File(directory))
        parseFilesAndFlags(tail)
      }
      case "--backend" :: "princess" :: tail => {
        parseFilesAndFlags(tail)
      }
      case "--backend" :: "nuxmv" :: tail => {
        backend = ChooseNuxmv
        parseFilesAndFlags(tail)
      }
      case "--backend" :: other :: _ => {
        throw new IllegalArgumentException(s"Unknown backend: ${other}!")
      }
      case other :: tail => {
        inputFiles ++= expandFileNameOrDirectoryOrGlob(other)
        parseFilesAndFlags(tail)
      }
    }
  }

  def parseMode(args: List[String]): Unit = args match {
    case Nil                       => throw new Exception("Error: No mode specified! \n\n" + usage)
    case "--" :: tail              => parseMode(tail)
    case "--help" :: _ | "-h" :: _ => throw new Exception(usage)
    case "solve-satisfy" :: rest   => parseFilesAndFlags(rest)
    case "find-image" :: rest => {
      runMode = FindImage
      parseFilesAndFlags(rest)
    }
    case other :: _ =>
      throw new Exception(s"Error: Invalid mode `${other}`!\n\n" + usage)
  }

  def parse(args: Array[String]): Try[CommandLineOptions] = Try {

    parseMode(args.toList)

    CommandLineOptions(
      inputFiles = inputFiles,
      timeout_ms = timeout_ms,
      trace = trace,
      dumpSMTDir = dumpSMTDir,
      runMode = runMode,
      backend = backend
    )
  }
}
