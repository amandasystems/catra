package uuverifiers.catra
import ap.terfor.ConstantTerm
import ap.parser.{IFormula, ITerm, ITimes, IBoolLit}
import java.math.BigInteger
import uuverifiers.common.{
  SymbolicLabel,
  IntState,
  Automaton,
  AutomatonBuilder,
  Tracing
}
import uuverifiers.common.AutomataTypes.State

sealed case class Constant(value: Int) extends Term {
  override def toPrincess(counterConstants: Map[Counter, ConstantTerm]): ITerm =
    value
  override def negate() = Constant(value * -1)
}

sealed case class Counter(name: String) extends Term {
  override def toPrincess(counterConstants: Map[Counter, ConstantTerm]): ITerm =
    counterConstants(this)
  override def negate() = CounterWithCoefficient(-1, this)
}

sealed abstract class Atom extends Formula {
  def negated(): Atom
}
sealed case class Inequality(
    lhs: Term,
    inequality: InequalitySymbol,
    rhs: Term,
    isPositive: Boolean = true
) extends Atom {
  def negated(): Inequality =
    Inequality(this.lhs, this.inequality, this.rhs, !this.isPositive)

  override def toPrincess(counterConstants: Map[Counter, ConstantTerm]) = {
    val left = lhs.toPrincess(counterConstants)
    val right = rhs.toPrincess(counterConstants)

    inequality match {
      case LessThan           => left < right
      case GreaterThan        => left > right
      case Equals             => left === right
      case GreaterThanOrEqual => left >= right
      case LessThanOrEqual    => left <= right
      case NotEquals          => left =/= right
    }
  }
}

sealed case class TrueOrFalse(isTrue: Boolean) extends Atom with Formula {
  override def negated(): TrueOrFalse = TrueOrFalse(!isTrue)
  override def toPrincess(
      counterConstants: Map[Counter, ConstantTerm]
  ): IFormula = IBoolLit(isTrue)
}

sealed trait Term {
  def toPrincess(counterConstants: Map[Counter, ConstantTerm]): ITerm
  def negate(): Term
}
sealed case class CounterWithCoefficient(coefficient: Int, counter: Counter)
    extends Term {
  override def toPrincess(counterConstants: Map[Counter, ConstantTerm]): ITerm =
    ITimes(coefficient, counterConstants(counter))
  override def negate() =
    if (coefficient == -1) counter
    else CounterWithCoefficient(coefficient * -1, counter)
}

sealed case class Sum(terms: Seq[Term]) extends Term {
  def toPrincess(
      counterConstants: Map[Counter, ConstantTerm]
  ): ITerm = terms.map(_.toPrincess(counterConstants)).reduce(_ +++ _)

  def negate(): Sum = Sum(terms.map(_.negate()))

}

sealed trait InequalitySymbol
case object LessThan extends InequalitySymbol
case object GreaterThan extends InequalitySymbol
case object Equals extends InequalitySymbol
case object GreaterThanOrEqual extends InequalitySymbol
case object LessThanOrEqual extends InequalitySymbol
case object NotEquals extends InequalitySymbol

sealed trait Formula extends DocumentFragment {
  def negated(): Formula
  def toPrincess(counterConstants: Map[Counter, ConstantTerm]): IFormula
  // TODO
  def accepts(counterValues: Map[Counter, BigInteger]): Boolean = ???
}

sealed case class And(left: Formula, right: Formula) extends Formula {
  override def negated() = Or(left.negated(), right.negated())
  override def toPrincess(
      counterConstants: Map[Counter, ConstantTerm]
  ): IFormula =
    left.toPrincess(counterConstants) &&& right.toPrincess(counterConstants)

}
sealed case class Or(left: Formula, right: Formula) extends Formula {
  override def negated() = And(left.negated(), right.negated())
  override def toPrincess(
      counterConstants: Map[Counter, ConstantTerm]
  ): IFormula =
    left.toPrincess(counterConstants) ||| right.toPrincess(counterConstants)
}

sealed trait AutomatonFragment
sealed case class Transition(
    from: String,
    to: String,
    label: SymbolicLabel,
    counterIncrements: Map[Counter, Int]
) extends AutomatonFragment
sealed case class InitialState(name: String) extends AutomatonFragment
sealed case class AcceptingStates(names: Seq[String]) extends AutomatonFragment

object WhyCantIDefineGlobalTypeAliasesGoddammit {
  type TransitionToCounterOffsets =
    Map[(State, SymbolicLabel, State), Map[Counter, Int]]
}

import WhyCantIDefineGlobalTypeAliasesGoddammit.TransitionToCounterOffsets

sealed trait DocumentFragment

sealed case class CounterDefinition(counters: Seq[Counter])
    extends DocumentFragment

sealed case class AutomatonGroup(automata: Seq[NamedCounterAutomaton])
    extends DocumentFragment

sealed case class NamedCounterAutomaton(
    name: String,
    automaton: Automaton,
    offsets: TransitionToCounterOffsets
)

class InputFileParser extends Tracing {
  import fastparse._
  import JavaWhitespace._

  private val interner = new Interner()

  def automatonFromFragments(
      fragments: Seq[AutomatonFragment]
  ): (Automaton, TransitionToCounterOffsets) = {
    val builder = AutomatonBuilder()
    var counterOffsets: TransitionToCounterOffsets = Map()

    interner.freshNamespace()

    for (fragment <- fragments) {
      fragment match {
        case AcceptingStates(names) => {
          val nameIds =
            names.map(interner.getOrUpdate(_)).map(IntState(_)).toSeq
          builder.addStates(nameIds)
          nameIds.foreach(builder.setAccepting(_))
        }
        case InitialState(name) => {
          builder.addStates(Seq(IntState(interner.getOrUpdate(name))))
          builder.setInitial(IntState(interner.getOrUpdate(name)))
        }
        case Transition(from, to, label, counterIncrements) => {
          val fromIdx = IntState(interner.getOrUpdate(from))
          val toIdx = IntState(interner.getOrUpdate(to))
          builder.addStates(Seq(fromIdx, toIdx))
          val transition = (fromIdx, label, toIdx)
          builder.addTransition(transition)
          counterOffsets += ((transition, counterIncrements))
        }
      }
    }
    (builder.getAutomaton(), counterOffsets)
  }

  // TODO ensure register offsets are on disjoint transitions
  // TODO ensure register offsets only increment declared registers
  def documentToInstance(fragments: Seq[DocumentFragment]): Instance =
    trace("documentToInstance") {
      var groupedAutomata: Seq[Seq[Automaton]] = Seq()
      var transitionToOffsets: TransitionToCounterOffsets = Map()
      var counters = List[Counter]()
      var constraints = List[Formula]()

      for (fragment <- fragments) {
        fragment match {
          // FIXME warn about empty groups!
          case AutomatonGroup(a) if a.isEmpty => ()
          case AutomatonGroup(group) => {
            groupedAutomata =
              groupedAutomata.appended(group.map(_.automaton).toSeq)
            group.foreach { a =>
              a.offsets.foreach(transitionToOffsets += _)
            }
          }
          case cs: CounterDefinition => counters ++= cs.counters
          case f: Formula            => constraints ::= f
        }
      }
      Instance(counters, groupedAutomata, transitionToOffsets, constraints)
    }

  def digit[_ : P] = P(CharIn("0-9"))
  def asciiLetter[_ : P] = CharIn("A-Z") | CharIn("a-z") | "_"

  def counterType[_ : P] = P("int").!

  def constant[_ : P]: P[Int] =
    P("-".? ~ ("0" | (CharIn("1-9") ~ digit.rep(0)))).!.map(_.toInt)

  // FIXME I don't like how NotEquals isn't negated equals, but there is no
  // clean way I can think of to fix it.
  def atom[_ : P]: P[Atom] =
    P(
      (sum ~ inequalitySymbol ~ sum).map {
        case (lhs, inequality, rhs) => {
          ap.util.Timeout.check
          Inequality(lhs, inequality, rhs)
        }
      }
        | "true".!.map(_ => TrueOrFalse(true))
        | "false".!.map(_ => TrueOrFalse(false))
    )

  def inequalitySymbol[_ : P]: P[InequalitySymbol] =
    P(
      "=".!.map(_ => Equals)
        | ">=".!.map(_ => GreaterThanOrEqual)
        | ">=".!.map(_ => LessThanOrEqual)
        | ">".!.map(_ => GreaterThan)
        | "<".!.map(_ => LessThan)
        | "!=".!.map(_ => NotEquals)
    )

  def constantOrIdentifier[_ : P]: P[Term] =
    P(
      (constant ~ "*".? ~ identifier.!).map {
        case (k, x) =>
          CounterWithCoefficient(k, Counter(x))
      }
        | constant.map(Constant(_))
        | "-" ~~ identifier.!.map(x => CounterWithCoefficient(-1, Counter(x)))
        | identifier.!.map(Counter(_))
    )

  def sum[_ : P]: P[Sum] =
    P(
      (constantOrIdentifier ~ (CharIn("+\\-").! ~ constantOrIdentifier).rep())
        .map {
          case (first, signAndTerms) =>
            Sum(first +: signAndTerms.map {
              case ("+", positiveTerm) => positiveTerm
              case ("-", negativeTerm) => negativeTerm.negate()
            })
        }
        | constantOrIdentifier.map(t => Sum(Seq(t)))
    )

  def unaryExpression[_ : P]: P[Formula] =
    P(
      ("!" ~ term).map(_.negated())
        | atom
    )

  // TODO use an enumeration for connective symbols to convince the compiler we
  // know what we're doing.
  def connective[_ : P]: P[String] = P("&&" | "||").!

  def paren[_ : P]: P[Formula] = P("(" ~ formula ~ ")")

  def term[_ : P]: P[Formula] = P(unaryExpression | paren)

  def binaryExpression[_ : P]: P[Formula] =
    P(term ~ connective ~ formula).map { // Match is known to be exhaustive.
      case (l, "&&", r) => And(l, r)
      case (l, "||", r) => Or(l, r)
    }

  def formula[_ : P]: P[Formula] = P(binaryExpression | term)

  def sequenceOfIdentifiers[_ : P]: P[Seq[String]] =
    P(identifier.rep(sep = ",", min = 1))

  def init[_ : P]: P[InitialState] =
    P("init" ~ identifier ~ ";").map(InitialState(_))
  def accepting[_ : P]: P[AcceptingStates] =
    P("accepting" ~ sequenceOfIdentifiers ~ ";").map(AcceptingStates(_))
  def labelRange[_ : P]: P[SymbolicLabel] =
    (P(
      "[" ~
        (
          (constant ~ "," ~ constant).map {
            case (lower, upper) =>
              SymbolicLabel.CharRange(lower.toChar, upper.toChar)
          }
            | constant.map(c => SymbolicLabel.SingleChar(c.toChar))
        )
        ~
          "]"
    ))
  def incrementOrDecrement[_ : P]: P[Int] =
    P(
      ("+".!.map(_ => 1)
        | "-".!.map(_ => -1))
        ~ P("=")
    )
  def counterOperation[_ : P]: P[(Counter, Int)] =
    P(identifier ~ incrementOrDecrement ~ constant).map {
      case (counterName, coefficient, offset) =>
        (Counter(counterName), coefficient * offset)
    }
  def counterIncrements[_ : P]: P[Seq[(Counter, Int)]] =
    P("{" ~ counterOperation.rep(min = 0, sep = ",") ~ "}")
  def transition[_ : P]: P[Transition] =
    P(identifier ~ "->" ~ identifier ~ labelRange ~ counterIncrements.? ~ ";")
      .map {
        case (from, to, label, increments) =>
          Transition(from, to, label, increments.getOrElse(Map()).toMap)
      }

  def constraintDefinition[_ : P]: P[Formula] = P("constraint" ~/ formula)
  def automatonBody[_ : P]: P[(Automaton, TransitionToCounterOffsets)] =
    P("{" ~ (init | accepting | transition).rep ~ "}")
      .map(automatonFromFragments(_))

  def automatonDefinition[_ : P]: P[NamedCounterAutomaton] =
    P("automaton" ~/ identifier ~ automatonBody).map {
      case (name, (a, offsets)) => NamedCounterAutomaton(name, a, offsets)
    }

  /**
   * An identifer is any combination of letters and numbers, starting with a
   * letter.
   */
  def identifier[_ : P]: P[String] =
    P(asciiLetter.rep(1) ~ (digit | asciiLetter | "_").rep(0)).!
  def counterDefinition[_ : P]: P[CounterDefinition] =
    P(
      "counter" ~/ counterType ~ identifier.rep(sep = ",", min = 1)
    ).map {
      case (_, counters) => {
        // TODO handle types when we have them.
        CounterDefinition(counters.map(Counter(_)))
      }
    }

  def productDefinition[_ : P]: P[AutomatonGroup] = {
    P("synchronised" ~/ "{" ~ (automatonDefinition ~ ";").rep() ~ "}")
      .map(AutomatonGroup(_))
  }

  def expression[_ : P]: P[DocumentFragment] =
    P(
      counterDefinition | constraintDefinition | automatonDefinition.map(
        a => AutomatonGroup(Seq(a))
      )
        | productDefinition
    )
  def document[_ : P]: P[Instance] =
    P((expression ~ ";").rep(1)).map(documentToInstance(_))
  def parser[_ : P]: P[Instance] = P(" ".rep ~ document ~ End)
}

object InputFileParser {
  def parse(s: String): fastparse.Parsed[Instance] = {
    val p = new InputFileParser()
    ap.util.Timeout.withTimeoutMillis(10000) {
      fastparse.parse(s, p.parser(_))
    } { fastparse.parse("parsing timeout", p.parser(_)) }
  }
}

class Interner {
  var currentIndex = 0
  var nameToStateIdx: Map[String, Int] = Map()
  var namespaceOffset = 0

  def freshNamespace() = {
    namespaceOffset += 1
  }

  def getOrUpdate(name: String): Int = {
    val expandedName = s"${namespaceOffset}.${name}"
    nameToStateIdx.get(expandedName) match {
      case Some(index) => index
      case None => {
        nameToStateIdx += (expandedName -> currentIndex)
        currentIndex += 1
        currentIndex - 1
      }
    }
  }
}
