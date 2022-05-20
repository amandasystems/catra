package uuverifiers.catra

import ap.SimpleAPI
import ap.terfor.ConstantTerm

import scala.util.{Failure, Success}
import uuverifiers.common.{Counting, State, SymbolicLabel, Tracing}

import java.io.{
  BufferedReader,
  File,
  InputStreamReader,
  OutputStreamWriter,
  PrintWriter
}
import scala.util.Try
import java.util.concurrent.TimeUnit
import java.math.BigInteger

class NUXMVBackend(private val arguments: CommandLineOptions) extends Backend {
  override def findImage(instance: Instance) = ???
  override def solveSatisfy(instance: Instance) =
    new NUXMVInstance(arguments, instance).result

}

class NUXMVInstance(arguments: CommandLineOptions, instance: Instance)
    extends Tracing {

  import instance._
  val baseCommand = Array("nuxmv", "-int")
  val Unreachable = """^-- invariant block .* is true$""".r
  val Reachable = """^-- invariant block .* is false$""".r
  val CounterValue = """^    counter_(\d+) = (\d+)$""".r

  val nuxmvCmd = arguments.timeout_ms match {
    case Some(timeout_ms) =>
      Array("timeout", "--foreground", s"${timeout_ms.toFloat / 1000}s") ++ baseCommand
    case None => baseCommand

  }

  trace("nuxmv command line")(nuxmvCmd.mkString(" "))

  val outFile =
    File.createTempFile("parikh-", ".smv")

  val blockNum =
    automataProducts.size
  val automataStates: Seq[Seq[IndexedSeq[State]]] =
    for (auts <- automataProducts)
      yield (for (aut <- auts) yield aut.states.toIndexedSeq)
  val stateNums: Seq[Seq[Int]] =
    for (auts <- automataStates) yield (auts map (_.size))
  val automataCounters: Seq[Seq[Seq[Counter]]] =
    for (auts <- automataProducts) yield for (a <- auts) yield {
      a.counters()
        .toSet
        .toIndexedSeq
        .sortBy((c: Counter) => c.name)
    }

  val stateVars: Seq[IndexedSeq[String]] =
    for ((auts, n) <- automataStates.zipWithIndex)
      yield (for (m <- auts.indices) yield "state_" + n + "_" + m)
  val inputVar =
    "l"
  val blockVar =
    "block"
  val counterVars: Map[Counter, String] =
    (for ((cnt, n) <- counters.zipWithIndex)
      yield (cnt -> ("counter_" + n))).toMap
  val counterAssignments: Array[BigInteger] = Array.ofDim(counters.size)

  val falseF = "0 = 1"
  val trueF = "0 = 0"

  private def intEnumType(n: Int): String =
    "{ " + (for (i <- 0 until (n max 2)) yield ("" + i)).mkString(", ") + " }"

  private def and(fors: String*): String =
    if (fors.isEmpty)
      trueF
    else
      (for (f <- fors) yield "(" + f + ")") mkString " & "

  private def or(fors: String*): String =
    if (fors.isEmpty)
      falseF
    else
      (for (f <- fors) yield "(" + f + ")") mkString " | "

  private def eq(t1: String, t2: String): String =
    t1 + " = " + t2

  private def eq(t1: String, t2: Int): String =
    t1 + " = " + t2

  private def unchanged(t: String): String =
    next(t) + " = " + t

  private def next(t: String): String =
    "next(" + t + ")"

  private def inLabel(t: String, l: SymbolicLabel): String = l match {
    case SymbolicLabel.NoChar        => falseF
    case SymbolicLabel.SingleChar(c) => eq(t, c)
    case SymbolicLabel.CharRange(lower, upper) =>
      and("" + lower.toInt + " <= " + t, "" + t + " <= " + upper.toInt)
    case SymbolicLabel.AnyChar => trueF
  }

  val counterSubst: Map[Counter, ConstantTerm] =
    for ((c, v) <- counterVars) yield c -> new ConstantTerm(v)

  def printNUXMVModule(): Unit = {
    println("MODULE main")

    println("IVAR")
    println("  " + inputVar + " : integer;")

    println("VAR")
    println(
      "  " + blockVar + " : " + intEnumType(automataStates.size + 1) + ";"
    )
    for ((v, states) <- stateVars.flatten zip automataStates.flatten)
      println("  " + v + " : " + intEnumType(states.size) + ";")
    for (cnt <- counters)
      println("  " + counterVars(cnt) + " : integer;")

    println("ASSIGN")
    println("  init(" + blockVar + ") := 0;")
    for (((v, aut), states) <- stateVars.flatten zip automataProducts.flatten zip automataStates.flatten)
      println("  init(" + v + ") := " + (states indexOf aut.initialState) + ";")
    for (cnt <- counters)
      println("  init(" + counterVars(cnt) + ") := 0;")

    println("TRANS")

    val autTransitions =
      for (blockId <- 0 until blockNum) yield {
        val blockAutomata = automataProducts(blockId)
        val blockAutomataStates = automataStates(blockId)
        val blockAutomataVars = stateVars(blockId)

        and(
          eq(blockVar, blockId),
          unchanged(blockVar),
          and(
            (for ((vars, n) <- stateVars.zipWithIndex;
                  if n != blockId;
                  v <- vars)
              yield unchanged(v)): _*
          ),
          and(
            (for ((counters, n) <- automataCounters.zipWithIndex;
                  if n != blockId;
                  cs <- counters; c <- cs)
              yield unchanged(counterVars(c))): _*
          ),
          and((for (autId <- blockAutomata.indices) yield {
            val aut = blockAutomata(autId)
            val states = blockAutomataStates(autId)
            val stateVar = blockAutomataVars(autId)
            val counters = aut.counters().toIndexedSeq.sortBy(_.name)

            or(
              (for (trip <- aut.transitions) yield {
                and(
                  eq(stateVar, states indexOf trip.from()),
                  eq(next(stateVar), states indexOf trip.to()),
                  inLabel(inputVar, trip.label()),
                  and((for (c <- counters) yield trip.increments(c) match {
                    case Some(offset) =>
                      eq(next(counterVars(c)), counterVars(c) + " + " + offset)
                    case None =>
                      unchanged(counterVars(c))
                  }): _*)
                )
              }): _*
            )
          }): _*)
        )
      }

    val blockTransitions =
      for (blockId <- 0 until blockNum) yield {
        and(
          eq(blockVar, blockId),
          eq(next(blockVar), blockId + 1),
          and((for (v <- stateVars.flatten) yield unchanged(v)): _*),
          and((for (v <- counterVars.values.toSeq) yield unchanged(v)): _*),
          and(
            (for (((v, aut), states) <- stateVars(blockId) zip automataProducts(
                    blockId
                  ) zip automataStates(
                    blockId
                  ))
              yield or(
                (for (s <- states; if aut isAccept s)
                  yield eq(v, states indexOf s)): _*
              )): _*
          ),
          if (blockId == blockNum - 1)
            and(
              (for (c <- constraints)
                yield SimpleAPI.pp(c.toPrincess(counterSubst))): _*
            )
          else
            trueF
        )
      }

    println("  " + or((autTransitions ++ blockTransitions): _*))

    println("INVARSPEC")
    println("  " + blockVar + " != " + blockNum + ";")
  }

  val result: Try[SatisfactionResult] =
    try {
      val out = new java.io.FileOutputStream(trace("nuxmv model")(outFile))
      Console.withOut(out) {
        printNUXMVModule()
      }
      out.close

      val process = Runtime.getRuntime.exec(nuxmvCmd)
      val stdin = process.getOutputStream
      val stderr = process.getErrorStream
      val stdout = process.getInputStream

      val stdinWriter = new PrintWriter(new OutputStreamWriter(stdin))
      val stdoutReader = new BufferedReader(new InputStreamReader(stdout))

      def sendCommand(cmd: String): Unit = {
        stdinWriter.println(trace("nuxmv <<")(cmd))
        stdinWriter.flush
      }

      def readLine: String = stdoutReader.readLine

      sendCommand("read_model -i " + outFile + ";")
      sendCommand("flatten_hierarchy;")
      sendCommand("encode_variables;")
      sendCommand("go_msat;")
      sendCommand("check_invar_ic3;")
      sendCommand("quit;")

      // FIXME this is essentially a terrible implementation of a two-step state
      // machine that first looks for SAT/UNSAT, then assignments. Doing it like
      // this is ugly, but works (tm), sort of by accident.
      val result: Try[SatisfactionResult] = {
        var cont = true
        var result: Try[SatisfactionResult] = Failure(
          new Exception("No output from nuxmv")
        )
        while (cont) {
          cont = trace("nuxmv >>")(readLine) match {
            case null => {
              // The process has closed the stream. Wait for it to finish, but
              // don't wait for too long and kill it if it's too slow.
              val didExit = process.waitFor(1, TimeUnit.SECONDS)
              if (!trace("dying process did exit")(didExit)) {
                // Wait for the process to really, really exit.
                process.destroyForcibly().waitFor()
              }
              false // We're done!
            }
            case Unreachable() => {
              result = Success(Unsat)
              false // There's nothing more to parse.
            }
            // TODO: parse the model
            case Reachable() => {
              result = Success(Sat(Map.empty))
              true // Capture the model assignment
            }
            case CounterValue(counter, value) => {
              counterAssignments(counter.toInt) = new BigInteger(value)
              true
            }
            case _ => true
          }
        }
        result match {
          case Success(Sat(_)) => {
            Success(Sat(counters.zip(counterAssignments).toMap))
          }
          case other => other
        }
      }

      stdinWriter.close
      stdoutReader.close
      stderr.close

      if (!trace("nuxmv still running?")(process.isAlive())) {
        // 124 is the exit with timeout code for timeout
        if (trace("exitValue")(process.exitValue()) == 124) {
          Success(Timeout(arguments.timeout_ms.get))
        } else {
          result
        }
      } else {
        process.destroyForcibly()
        result
      }
    } finally {
      outFile.delete
    }
}
