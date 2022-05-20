import org.scalatest.funsuite.AnyFunSuite
import uuverifiers.common.MapGraph._

class TestGraphOperations extends AnyFunSuite {

  val allConnected =
    Map(1 -> List(1, 2, 3, 4), 2 -> List(2), 3 -> List(3, 2, 4), 4 -> List())

  val twoNodeCycle = Map(1 -> List(2), 2 -> List(1))

  test("Simple BFS with cycle iterates over all nodes") {
    assert((allConnected startBFSFrom 1).toSeq == List(1, 2, 3, 4))
  }

  test("BFS marks all nodes visited") {
    assert((allConnected startBFSFrom 1).visitAll().unvisitedNodes().isEmpty)
  }

  test("BFS misses disconnected bit") {
    val g =
      Map(1 -> List(1, 2, 3), 2 -> List(2), 3 -> List(3, 2), 4 -> List())

    assert((g startBFSFrom 1).visitAll().unvisitedNodes() == Set(4))

  }

  test("connectedComponent finds components in SCC-less graph") {
    val sccs = allConnected.stronglyConnectedComponents()
    assert(sccs == Set(Set(1), Set(2), Set(3), Set(4)))
  }

  test("connectedComponent finds simple 2-node component") {
    assert(twoNodeCycle.stronglyConnectedComponents() == Set(Set(1, 2)))
  }

  test(
    "connectedComponent reproduces first graph from Wikipedia:Strongly_connected_component"
  ) {
    val ex1 = Map(
      'a' -> List('b'),
      'b' -> List('c', 'e', 'f'),
      'c' -> List('d', 'g'),
      'e' -> List('a', 'f'),
      'f' -> List('g'),
      'g' -> List('f'),
      'd' -> List('h', 'c'),
      'h' -> List('d', 'g')
    )

    assert(
      ex1.stronglyConnectedComponents() == Set(
        Set('a', 'b', 'e'),
        Set('f', 'g'),
        Set('c', 'd', 'h')
      )
    )
  }

  test("simpleCycle finds a minimal cycle") {
    assert(twoNodeCycle.simpleCycles() == Set(Set(1, 2)))
  }

  test("simpleCycle finds a self-loop") {
    assert(Map(1 -> List(1)).simpleCycles() == Set(Set(1)))
  }

  test("simpleCycle finds a minimal cycle and a self-loop") {
    assert(
      Map(1 -> List(1, 2), 2 -> List(1))
        .simpleCycles() == Set(Set(1), Set(1, 2))
    )
  }

  test("simpleCycle finds two cycles") {
    val g = Map(1 -> List(2, 4), 2 -> List(3), 3 -> List(1), 4 -> List(1))

    assert(g.simpleCycles() == Set(Set(1, 2, 3), Set(1, 4)))
  }

  test("BFS finds last node of connected graph") {
    assert(allConnected.startBFSFrom(1).pathTo(4) == Some(Seq((1, (), 4))))
  }

  test("BFS does not find disconnected node") {
    val g = Map(1 -> List(2, 3), 2 -> List(2), 3 -> List(3), 4 -> List(4))

    assert(g.startBFSFrom(1).pathTo(4) == None)
  }

  test("BFS generates correct path of straight-line graph") {
    assert(
      Map(1 -> List(2), 2 -> List(3), 3 -> List())
        .startBFSFrom(1)
        .pathTo(3) == Some(Seq((1, (), 2), (2, (), 3)))
    )
  }

  test("minCut finds min cut of simple graph") {
    val g = Map(
      1 -> List(2, 3),
      2 -> List(4),
      3 -> List(4),
      4 -> List(5),
      5 -> List()
    )

    assert(g.minCut(1, 5) == Set((4, (), 5)))

  }

  test("minCut solves buggy example #1 correctly") {
    val g = Map(
      0 -> List(0, 1, 2, 3),
      1 -> List(1),
      2 -> List(2),
      3 -> List(3, 1, 2)
    )

    assert(g.minCut(0, 1) == Set((0, (), 1), (0, (), 3)))

  }

  test("minCut solves buggy example #2 correctly") {
    val g = Map(
      0 -> List(1),
      1 -> List(2),
      2 -> List(2, 3),
      3 -> List(3)
    )

    assert(g.minCut(0, 1) == Set((0, (), 1)))

  }

  test("minCut solves buggy example #3 correctly") {
    val g = Map(
      0 -> List(1),
      1 -> List(1, 2, 3),
      2 -> List(2, 4),
      3 -> List(3),
      4 -> List(3, 4)
    )

    assert(g.minCut(0, 4) == Set((0, (), 1)))

  }

  test("merge and min-cut bug does not occur") {
    val g = Map(
      (0 -> List(0, 1, 2)),
      (1 -> List(1, 3)),
      (2 -> List(2, 3, 1)),
      (3 -> List(3))
    )

    val gMerged = g.mergeNodes(Set(0, 2, 3))
    import gMerged.equivalentNode

    assert(g.minCut(0, 1) == Set((0, (), 1), (0, (), 2)))
    assert(gMerged.minCut(0, 1).flatMap(_._2) == Set((0, (), 1), (2, (), 1)))
  }

  test("merge path bug does not occur") {
    val g = Map(
      (0 -> List(0, 2)),
      (1 -> List(1, 3)),
      (2 -> List(2, 3, 1)),
      (3 -> List(3))
    )

    val gMerged = g.mergeNodes(Set(0, 2, 3))

    import gMerged.equivalentNode

    assert(
      gMerged.startBFSFrom(0).pathTo(1).map(_.flatMap(_._2)) == Some(
        List((2, (), 1))
      )
    )
  }

}
// // TODO property-based tests for "union of connected components contains all nodes"
