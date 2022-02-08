package uuverifiers.parikh_theory
import org.scalatest.funsuite.AnyFunSuite

class TestInputFileParser extends AnyFunSuite {

  def tryParse(input: String) = {
    import fastparse.Parsed.{Failure, Success}
    InputFileParser.parse(input) match {
      case Success(value, _) => value
      case Failure(_, _, extra) => {
        withClue(extra.trace().longMsg)(assert(false))
      }
    }
  }

  test("example input file can be parsed") {
    import scala.io.Source
    tryParse(Source.fromFile("input").mkString(""))
  }

  test("parse a constraint with and") {
    tryParse("constraint -2x = z && y > 3;")
  }

  test("parse a constraint with negated atom") {
    tryParse("constraint ¬-2x = 2;")
  }

  test("parse a comment") {
    tryParse("//Comment\nconstraint x = x;")
  }

  test("parse automaton block without transitions") {
    tryParse {
      """
          automaton A {
          | init s0;
          | accepting s0;
          |};
          """.stripMargin
    }
  }

  test("parse automaton block with transitions") {
    tryParse {
      """
          automaton A {
          | init s0;
          | s0 -> s1 [15];
          | s0 -> s1 [0, 10] { x += 1 , y -= 1};
          |};
          """.stripMargin
    }
  }

  test("parse several counters") {
    tryParse("counter int a, b, c;")
  }

  test("parse multiple variables on LHS of constraint") {
    tryParse("constraint x + y = z;")
  }

  test("parse multiple variables on RHS of constraint") {
    tryParse("constraint y = z + x;")
  }

  test("parse coefficients in constraint") {
    tryParse("constraint y = z + -x + -17r;")
  }

  test("parse constraint with parenthesis") {
    tryParse("constraint (y = z);")
  }

  test("parse constraint with three AND") {
    tryParse(
      "constraint all_7_0_len = aut_len_cnt_30 && all_7_0_len = aut_len_cnt_29 && all_7_0_len = aut_len_cnt_28;"
    )
  }

  test("parse constraint with coefficient and *") {
    tryParse("constraint (-1*all_1_0 + 1 >= 0);");
  }

  test("constraint with parentheses") {
    tryParse("constraint R1 = R40 && (R0 = 0 || R8 = 0);")
  }

  test("constraint with not equals") {
    tryParse("constraint R1 != R40;")
  }

  test("constraint with left side in parentheses") {
    tryParse("constraint (R0 != 0) && R0 != 0;")
  }

  test("constraint with right side in parentheses") {
    tryParse("constraint R0 != 0 && (R0 != 0);")
  }

  test("left side parenthesis is formula") {
    tryParse(
      "constraint (R11 != 0 && R0 = R12) && (R13 != 0);"
    )
  }

  test("full input file example") {
    tryParse(
      "constraint R1 = R40 && R23 = 0 && R24 = 0 && R25 = 0 && R26 = R40 && R39 = 0 && -1 < R0 && R2 < 1 && R5 < 1 && -1 < R40 && (R0 != 0 || R8 = 0 || (R11 = 0 && R12 = 0)) && (R0 != 0 || R8 = 0 || (R13 = 0 && R14 = 0)) && (R0 != 0 || R8 = 0 || (R15 = 0 && R16 = 0)) && (R11 != 0 || R0 = R12 || R0 < 1) && (R13 != 0 || R0 = R14 || R0 < 1) && (R15 != 0 || R0 = R16 || R0 < 1) && (R27 != 0 || R28 = R40 || (R0 = 0 && R40 = 0)) && (R29 != 0 || R30 = R40 || (R0 = 0 && R40 = 0)) && (R31 != 0 || R32 = R40 || (R0 = 0 && R40 = 0)) && (R33 != 0 || R34 = R40 || (R0 = 0 && R40 = 0)) && (R35 != 0 || R36 = R40 || (R0 = 0 && R40 = 0)) && (R37 != 0 || R38 = R40 || (R0 = 0 && R40 = 0)) && (R9 = 0 || (R21 = 0 && R22 = 0)) && (R10 = 0 || (R17 = 0 && R18 = 0)) && (R10 = 0 || (R19 = 0 && R20 = 0)) && (R11 = 0 || R0 < 1) && (R13 = 0 || R0 < 1) && (R15 = 0 || R0 < 1) && (R27 = 0 || (R0 = 0 && R40 = 0)) && (R29 = 0 || (R0 = 0 && R40 = 0)) && (R31 = 0 || (R0 = 0 && R40 = 0)) && (R33 = 0 || (R0 = 0 && R40 = 0)) && (R35 = 0 || (R0 = 0 && R40 = 0)) && (R37 = 0 || (R0 = 0 && R40 = 0));"
    )
  }

  test("parse complex sum") {
    tryParse("constraint R0 = R9 && R1 - R37 = 1;")
  }

  test("minus works as intended") {
    import fastparse.Parsed.Success

    val Success(instance, _) =
      InputFileParser.parse("constraint a - b + c = 0;")
    val Sum(terms) = instance.constraints(0).leftSide.asInstanceOf[Atom].lhs
    assert(
      terms.toSet == Set(
        Counter("a"),
        Counter("c"),
        CounterWithCoefficient(-1, Counter("b"))
      )
    )
  }

}
