package uuverifiers.parikh_theory

import ap.SimpleAPI
import ap.terfor.ConstantTerm
import scala.util.{Success, Failure, Try}

import java.io.{
  File,
  PrintWriter,
  OutputStreamWriter,
  InputStreamReader,
  BufferedReader
}
import scala.util.Try

class NUXMVBackend(private val arguments: CommandLineOptions) extends Backend {
  override def findImage(instance: Instance) = ???
  override def solveSatisfy(instance: Instance) = {
    new NUXMVInstance(instance).result match {
      // TODO parse the outputs and populate the map for SAT
      case Some(true)  => Success(Sat(Map.empty))
      case Some(false) => Success(Unsat)
      case None        => Failure(new Exception("Nuxmv returned no result"))
    }
  }
}
object NUXMVInstance {
  val nuxmvCmd = Array("nuxmv", "-int")
  val Unreachable = """^-- invariant block .* is true$""".r
  val Reachable = """^-- invariant block .* is false$""".r
}

class NUXMVInstance(instance: Instance) extends Tracing {

  import instance._
  import NUXMVInstance._

  val outFile =
    File.createTempFile("parikh-", ".smv")

  val blockNum =
    automata.size
  val automataStates =
    for (auts <- automata)
      yield (for (aut <- auts) yield aut.states.toIndexedSeq)
  val stateNums =
    for (auts <- automataStates) yield (auts map (_.size))
  val automataCounters =
    for (auts <- automataStates) yield {
      for (aut <- auts) yield {
        (for (((s1, _, s2), m) <- transitionToOffsets.iterator;
              if aut contains s1;
              (cnt, _) <- m.iterator)
          yield cnt).toSet.toIndexedSeq.sortBy((x: Counter) => x.name)
      }
    }

  val stateVars =
    for ((auts, n) <- automataStates.zipWithIndex)
      yield (for (m <- 0 until auts.size) yield "state_" + n + "_" + m)
  val inputVar =
    "l"
  val blockVar =
    "block"
  val counterVars =
    (for ((cnt, n) <- counters.zipWithIndex)
      yield (cnt -> ("counter_" + n))).toMap

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

  val counterSubst =
    (for ((c, v) <- counterVars) yield (c -> new ConstantTerm(v))).toMap

  def printNUXMVModule() = {
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
    for (((v, aut), states) <- stateVars.flatten zip automata.flatten zip automataStates.flatten)
      println("  init(" + v + ") := " + (states indexOf aut.initialState) + ";")
    for (cnt <- counters)
      println("  init(" + counterVars(cnt) + ") := 0;")

    println("TRANS")

    val autTransitions =
      for (blockId <- 0 until blockNum) yield {
        val blockAutomata = automata(blockId)
        val blockAutomataStates = automataStates(blockId)
        val blockAutomataVars = stateVars(blockId)
        val blockAutomataCounters = automataCounters(blockId)

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
          and((for (autId <- 0 until blockAutomata.size) yield {
            val aut = blockAutomata(autId)
            val states = blockAutomataStates(autId)
            val stateVar = blockAutomataVars(autId)
            val counters = blockAutomataCounters(autId)

            or(
              (for (trip @ (s1, l, s2) <- aut.transitions.toSeq;
                    offsets = transitionToOffsets(trip))
                yield and(
                  eq(stateVar, states indexOf s1),
                  eq(next(stateVar), states indexOf s2),
                  inLabel(inputVar, l),
                  and((for (c <- counters) yield (offsets get c) match {
                    case Some(offset) =>
                      eq(next(counterVars(c)), counterVars(c) + " + " + offset)
                    case None =>
                      unchanged(counterVars(c))
                  }): _*)
                )): _*
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
            (for (((v, aut), states) <- stateVars(blockId) zip automata(blockId) zip automataStates(
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

  val result: Option[Boolean] =
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
        stdinWriter.println(cmd)
        stdinWriter.flush
      }

      def readLine: String = stdoutReader.readLine

      sendCommand("read_model -i " + outFile + ";")
      sendCommand("flatten_hierarchy;")
      sendCommand("encode_variables;")
      sendCommand("go_msat;")
      sendCommand("check_invar_ic3;")
      sendCommand("quit;")

      var result: Option[Boolean] = None
      var cont = true

      while (cont && result.isEmpty) trace("nuxmv >>")(readLine) match {
        case null =>
          cont = false
        case Unreachable() =>
          result = Some(false)
        case Reachable() => result = Some(true)
        case str         =>
      }

      stdinWriter.close
      stdoutReader.close
      stderr.close

      result
    } finally {
      outFile.delete
      None
    }
}
