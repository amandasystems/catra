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
          | s0 -> s1 [0, 10] { x += 1 ; y -= 1};
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

}
