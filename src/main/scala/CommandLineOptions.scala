package uuverifiers.parikh_theory
import scala.util.Try
import java.nio.file.FileSystems
import java.nio.file.SimpleFileVisitor
import java.nio.file.Files
import java.nio.file.Paths
import java.nio.file.Path
import java.nio.file.FileVisitResult
import java.nio.file.attribute.BasicFileAttributes
import java.io.IOException

sealed case class CommandLineOptions(
    inputFiles: Seq[String],
    timeout_ms: Option[Long],
    trace: Boolean
) {}

object CommandLineOptions {
  private val fileSystem = FileSystems.getDefault()
  private val fileExtension = ".par"

  /// Option fields
  private var timeout_ms: Option[Long] = None
  private var trace = false
  private var inputFiles: Seq[String] = Seq()

  private val usage =
    s"""
    Usage: <subcommand> <options> <files or directories>

    Available subcommands:
      solve-satisfy -- look for a satisfying solution
      find-image -- generate the full Parikh image in Presburger format
          NOT IMPLEMENTED!
    
    Available options:
      --trace -- generate a trace of the computation into trace.tex,
                  plus various .dot files. (default = ${trace})
      --timeout milliseconds -- set the timeout in ms (default = ${timeout_ms})
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
      case "--trace" :: _            => ???
      case "--timeout" :: milliseconds :: tail => {
        timeout_ms = Some(milliseconds.toLong)
        parseFilesAndFlags(tail)
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
    case "find-image" :: rest      => ???
    case other :: _ =>
      throw new Exception(s"Error: Invalid mode `${other}`!\n\n" + usage)
  }

  def parse(args: Array[String]): Try[CommandLineOptions] = Try {

    parseMode(args.toList)

    CommandLineOptions(
      inputFiles = inputFiles,
      timeout_ms = timeout_ms,
      trace = trace
    )
  }
}
