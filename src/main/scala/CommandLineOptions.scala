package uuverifiers.parikh_theory
import scala.util.{Try}
import java.nio.file.PathMatcher
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
    verbose: Boolean // TODO
) {}

object CommandLineOptions {
  private val fileSystem = FileSystems.getDefault()
  private val fileExtension = ".par"

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

    if (expandedHomePath.toFile().isDirectory()) {
      enumerateDirectory(expandedHomePath)
    } else Seq(expandedHomePath.toString())
  }
  def parse(args: Array[String]): Try[CommandLineOptions] = Try {
    CommandLineOptions(
      inputFiles = args.toList.tail.flatMap(expandFileNameOrDirectoryOrGlob),
      verbose = false
    )
  }
}
