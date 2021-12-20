package uuverifiers.parikh_theory
import ap.terfor.ConstantTerm
import ap.parser.{IFormula, ITerm, ITimes}

sealed case class Constant(value: Int) extends Term {
  override def toPrincess(counterConstants: Map[Counter, ConstantTerm]): ITerm =
    value
}

sealed case class Counter(name: String) extends Term {
  override def toPrincess(counterConstants: Map[Counter, ConstantTerm]): ITerm =
    counterConstants(this)
}
sealed case class Atom(
    lhs: Sum,
    inequality: Inequality,
    rhs: Sum,
    isPositive: Boolean = true
) extends Formula {
  def negated(): Atom =
    Atom(this.lhs, this.inequality, this.rhs, !this.isPositive)

  override def toPrincess(counterConstants: Map[Counter, ConstantTerm]) = {
    val left = lhs.toPrincess(counterConstants)
    val right = rhs.toPrincess(counterConstants)

    inequality match {
      case LessThan    => left < right
      case GreaterThan => left > right
      case Equals      => left === right
    }
  }
}

sealed trait Term {
  def toPrincess(counterConstants: Map[Counter, ConstantTerm]): ITerm
}
sealed case class CounterWithCoefficient(coefficient: Int, counter: Counter)
    extends Term {
  override def toPrincess(counterConstants: Map[Counter, ConstantTerm]): ITerm =
    ITimes(coefficient, counterConstants(counter))
}

sealed case class Sum(terms: Seq[Term]) {
  def toPrincess(
      counterConstants: Map[Counter, ConstantTerm]
  ): ITerm = terms.map(_.toPrincess(counterConstants)).reduce(_ +++ _)
}

sealed trait Inequality
case object LessThan extends Inequality
case object GreaterThan extends Inequality
case object Equals extends Inequality

sealed trait Formula extends DocumentFragment {
  def toPrincess(counterConstants: Map[Counter, ConstantTerm]): IFormula
}

sealed case class And(left: Atom, right: Atom) extends Formula {

  override def toPrincess(
      counterConstants: Map[Counter, ConstantTerm]
  ): IFormula =
    left.toPrincess(counterConstants) &&& right.toPrincess(counterConstants)

}
sealed case class Or(left: Atom, right: Atom) extends Formula {

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
    Map[(Int, SymbolicLabel, Int), Map[Counter, Int]]
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

sealed case class Instance(
    counters: Seq[Counter],
    automata: Seq[Seq[Automaton]],
    // These are global because we ensure all automata have mutually independent state IDs!
    transitionToOffsets: TransitionToCounterOffsets,
    constraints: Seq[Formula]
)

object InputFileParser {
  import fastparse._
  import JavaWhitespace._

  def automatonFromFragments(
      fragments: Seq[AutomatonFragment]
  ): (Automaton, TransitionToCounterOffsets) = {
    val builder = AutomatonBuilder()
    var counterOffsets: TransitionToCounterOffsets = Map()

    Interner.freshNamespace()

    for (fragment <- fragments) {
      fragment match {
        case AcceptingStates(names) => {
          val nameIds = names.map(Interner.getOrUpdate(_)).toSeq
          builder.addStates(nameIds)
          nameIds.foreach(builder.setAccepting(_))
        }
        case InitialState(name) => {
          builder.addStates(Seq(Interner.getOrUpdate(name)))
          builder.setInitial(Interner.getOrUpdate(name))
        }
        case Transition(from, to, label, counterIncrements) => {
          val fromIdx = Interner.getOrUpdate(from)
          val toIdx = Interner.getOrUpdate(to)
          builder.addStates(Seq(fromIdx, toIdx))
          val transition = (fromIdx, label, toIdx)
          builder.addTransitionTuple(transition)
          counterOffsets += ((transition, counterIncrements))
        }
      }
    }
    (builder.getAutomaton(), counterOffsets)
  }

  def documentToInstance(fragments: Seq[DocumentFragment]): Instance = {
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
          group.foreach{a => a.offsets.foreach(transitionToOffsets += _)}
        }
        case cs: CounterDefinition => counters ++= cs.counters
        case f: Formula            => constraints ::= f
      }
    }
    Instance(counters, groupedAutomata, transitionToOffsets, constraints)
  }

  def digit[_ : P] = P(CharIn("0-9"))
  def asciiLetter[_ : P] = CharIn("A-Z") | CharIn("a-z")

  def counterType[_ : P] = P("int").!

  def constant[_ : P]: P[Int] =
    P("-".? ~ ("0" | (CharIn("1-9") ~ digit.rep(0)))).!.map(_.toInt)

  def atom[_ : P]: P[Atom] = (sum ~ inequalitySymbol ~ sum).map {
    case (lhs, inequality, rhs) => Atom(lhs, inequality, rhs)
  }

  def inequalitySymbol[_ : P]: P[Inequality] =
    P(
      "=".!.map(_ => Equals)
        | ">".!.map(_ => GreaterThan)
        | "<".!.map(_ => LessThan)
    )

  def constantOrIdentifier[_ : P]: P[Term] =
    P(
      (constant ~ identifier.!).map {
        case (k, x) =>
          CounterWithCoefficient(k, Counter(x))
      }
        | constant.map(Constant(_))
        | "-" ~ identifier.!.map(x => CounterWithCoefficient(-1, Counter(x)))
        | identifier.!.map(Counter(_))
    )

  def sum[_ : P]: P[Sum] =
    P(
      constantOrIdentifier
        .rep(min = 1, sep = "+")
        .map(Sum(_))
    )

  def negation[_ : P] = P("¬").map(_ => true)
  def atomOrNotAtom[_ : P]: P[Atom] = P(negation.? ~ atom).map {
    case (None, atom)    => atom
    case (Some(_), atom) => atom.negated()
  }

  def formula[_ : P]: P[Formula] =
    P(
      (atomOrNotAtom ~ "∧" ~ atomOrNotAtom)
        .map {
          case (left, right) => And(left, right)
        }
        | (atomOrNotAtom ~ "∨" ~ atomOrNotAtom)
          .map {
            case (left, right) => Or(left, right)
          }
        | atomOrNotAtom
    )

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
    P("{" ~ counterOperation.rep(min = 0, sep = ";") ~ "}")
  def transition[_ : P]: P[Transition] =
    P(identifier ~ "->" ~ identifier ~ labelRange ~ counterIncrements.? ~ ";")
      .map {
        case (from, to, label, increments) =>
          Transition(from, to, label, increments.getOrElse(Map()).toMap)
      }

  def constraintDefinition[_ : P]: P[Formula] = P("constraint" ~ formula)
  def automatonBody[_ : P]: P[(Automaton, TransitionToCounterOffsets)] =
    P("{" ~ (init | accepting | transition).rep ~ "}")
      .map(automatonFromFragments(_))

  def automatonDefinition[_ : P]: P[NamedCounterAutomaton] =
    P("automaton" ~ identifier ~ automatonBody).map {
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
      "counter" ~ counterType ~ identifier.rep(sep = ",", min = 1)
    ).map {
      case (_, counters) => {
        // TODO handle types when we have them.
        CounterDefinition(counters.map(Counter(_)))
      }
    }

  def productDefinition[_ : P]: P[AutomatonGroup] = {
    P("intersect" ~ "{" ~ (automatonDefinition ~ ";").rep() ~ "}")
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
  def parse(s: String): Parsed[Instance] = fastparse.parse(s, parser(_))
}

object Interner {
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
