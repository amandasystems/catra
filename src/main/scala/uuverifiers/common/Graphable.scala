package uuverifiers.common

import EdgeWrapper._
import PathWrapper._

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.mutable.{
  ArrayBuffer,
  HashMap => MHashMap,
  Queue => MQueue,
  Set => MSet
}
import scala.language.implicitConversions
import scala.math.min
import scala.collection.mutable.ArrayDeque

trait Graphable[Node, Label] {
  def outgoingEdges(node: Node): Seq[(Node, Label, Node)]
  def allNodes(): Seq[Node]
  def edges(): Seq[(Node, Label, Node)]
  def subgraph(selectedNodes: Set[Node]): Graphable[Node, Label]
  def hasNode(node: Node): Boolean = allNodes() contains node
  def dropEdges(edges: Set[(Node, Label, Node)]): Graphable[Node, Label]
  def addEdges(edges: Iterable[(Node, Label, Node)]): Graphable[Node, Label]

  /// Derived methods
  type Cycle = Set[Node]
  type Edge = (Node, Label, Node)

  sealed class BFSVisitor(
      val graph: Graphable[Node, Label],
      val startNodes: Seq[Node],
      val walkWhen: ((Node, Label, Node)) => Boolean
  ) extends Iterator[Node] {

    private val nodeUnseen = MSet(graph.allNodes(): _*)
    private val toVisit = MQueue[Node](startNodes: _*)
    private val connectingEdge =
      MHashMap[Node, Option[Edge]]().withDefaultValue(None)

    nodeUnseen --= startNodes

    override def hasNext = toVisit.nonEmpty

    override def next() = {
      val thisNode = toVisit.dequeue()

      for (edge <- graph.outgoingEdges(thisNode).filter(walkWhen)
           if nodeUnseen contains edge.to()) {
        nodeUnseen -= edge.to()
        toVisit enqueue edge.to()
        connectingEdge(edge.to()) = Some(edge)
      }

      thisNode
    }
    def unvisitedNodes(): Set[Node] = nodeUnseen.toSet
    def nodeVisited(node: Node) = !(nodeUnseen contains node)
    def pathTo(endNode: Node): Option[Seq[Edge]] = {
      if (!(graph hasNode endNode)) {
        return None
      }
      this.takeWhile(endNode.!=).foreach(identity)
      if (nodeVisited(endNode)) {

        @tailrec
        def walkBackwards(
            currentNode: Node,
            path: List[Edge]
        ): List[Edge] = connectingEdge(currentNode) match {
          case None                      => path
          case Some(edge @ (from, _, _)) => walkBackwards(from, (edge :: path))
        }

        Some(walkBackwards(endNode, List()))
      } else {
        None
      }
    }
    def visitAll() = {
      this.foreach(identity)
      this
    }
  }

  def startBFSFrom(startNode: Node) =
    new BFSVisitor(this, Seq(startNode), _ => true)

  def startBFSFrom(startNodes: Seq[Node]) =
    new BFSVisitor(this, startNodes, _ => true)

  def startBFSFrom(
      startNodes: Seq[Node],
      walkWhen: ((Node, Label, Node)) => Boolean
  ) =
    new BFSVisitor(this, startNodes, walkWhen)

  def startBFSFrom(
      startNode: Node,
      walkWhen: ((Node, Label, Node)) => Boolean
  ) =
    new BFSVisitor(this, Seq(startNode), walkWhen)

  def neighbours(node: Node): Seq[Node] = outgoingEdges(node).map(_.to())

  // Apply is what you'd expect
  def apply(n: Node) = neighbours(n)

  // Calculate the min-cut between the unweighted flow network between
  // source and drain. This uses Edmonds-Karp.
  def minCut(
      source: Node,
      drain: Node
  ): Set[(Node, Label, Node)] =
    minCut(Seq(source), drain, mayCut = (_: (Node, Label, Node)) => true)

  // Calculate the min-cut between the unweighted flow network between
  // source and drain. This uses Edmonds-Karp.
  // This version may fail to find a s/d cut if there is a path using
  // only transitions where mayCut is false. If mayCut is always true,
  // this is regular minCut.
  def minCut(
      source: Seq[Node],
      drain: Node,
      mayCut: ((Node, Label, Node)) => Boolean
  ): Set[(Node, Label, Node)] = {
    assert(!source.contains(drain), "source and drain must be different")
    @tailrec
    def findResidual(
        residual: MapGraph[Node, Label]
    ): MapGraph[Node, Label] =
      residual.startBFSFrom(source).pathTo(drain) match {
        case None => residual
        case Some(augmentingPath) if !augmentingPath.exists(mayCut) =>
          residual
        case Some(augmentingPath) =>
          findResidual(
            residual
              .dropEdges(augmentingPath.toSet.filter(mayCut))
              .addEdges(augmentingPath.reversePath())
          )
      }

    val residual = findResidual(
      new MapGraph(this.edges().filter(!_.isSelfEdge()))
    )

    val visitor = residual.startBFSFrom(source).visitAll()

    val reachableInResidual: Set[Node] =
      residual.allNodes().filter(visitor.nodeVisited).toSet

    val res = this
      .edges()
      .filter(
        e =>
          (reachableInResidual contains e.from()) &&
            !(reachableInResidual contains e.to())
      )
      .toSet

    // FIXME remove this!
    if (res.nonEmpty) {
      for (e <- res) {
        assert(mayCut(e), s"Cut uncuttable edge $e!")
      }
      val resultingPath =
        this.dropEdges(res).startBFSFrom(source).pathTo(drain)

      assert(
        resultingPath.isEmpty,
        s"Cut did not actually cut $source from $drain, there was a path: $resultingPath!"
      )
    }

    res
  }

  def unreachableFrom(
      startNode: Node,
      walkWhen: ((Node, Label, Node)) => Boolean = _ => true
  ): Set[Node] = {
    val visitor: BFSVisitor = startBFSFrom(startNode, walkWhen)
    visitor.foreach(identity) // perform iteration
    visitor.unvisitedNodes()
  }

  // Find the strongly connected components of a graph using Tarjan's
  // algorithm, adapted from Wikipedia's pseudocode.
  // FIXME this code is SO. UGLY.
  def stronglyConnectedComponents() = {
    var smallestFreeIndex = 0
    val depthIndex = new MHashMap[Node, Int]
    val lowLink = new MHashMap[Node, Int]
    val inCurrentComponent = new MHashMap[Node, Boolean]
    var currentComponent = List[Node]()
    val components = new ArrayBuffer[Set[Node]]

    def unvisited(node: Node) = !(depthIndex contains node)

    for (node <- allNodes() if unvisited(node)) {
      strongConnect(node)
    }

    def strongConnect(node: Node): Unit = {

      depthIndex(node) = smallestFreeIndex
      lowLink(node) = smallestFreeIndex
      smallestFreeIndex += 1
      currentComponent = node +: currentComponent
      inCurrentComponent(node) = true

      for (successor <- neighbours(node)) {
        if (unvisited(successor)) {
          strongConnect(successor)
          lowLink(node) = min(lowLink(node), lowLink(successor))
        } else if (inCurrentComponent.getOrElse(successor, false)) {
          // successor is in the current SCC, but if it is not on the stack,
          // then (v, w) is a cross-edge and must be ignored.
          lowLink(node) = min(lowLink(node), depthIndex(successor))
        }
      }

      // Generate a SCC!
      if (lowLink(node) == depthIndex(node)) {
        // pop everything from the stack, set onStack to inCurrentComponent to false

        val (component, afterComponent) =
          currentComponent.span(node != _) match {
            case (wholeComponent, List()) => (wholeComponent, List())
            case (beforeNode, thisNode +: afterNode) =>
              (beforeNode :+ thisNode, afterNode)
            case (_, _) =>
              (List(), List()) // This is to shut Scala up, rule 1 applies here too.
          }

        currentComponent = afterComponent
        component.foreach(inCurrentComponent(_) = false)
        components += component.toSet
      }

    }
    components.toSet

  }

  // Find all simple cycles in the graph. Uses Johnson's algorithm. Adapted from
  // networkx's Python version.
  def simpleCycles(): Set[Cycle] = {
    def unblock(
        thisNode: Node,
        blocked: MSet[Node],
        noCircuit: MHashMap[Node, MSet[Node]]
    ) = {
      val stack = ArrayDeque(thisNode)
      while (!stack.isEmpty) {
        val node = stack.removeHead()
        if (blocked contains node) {
          blocked -= node
          stack :++ noCircuit.getOrElse(node, Set())
          noCircuit -= node
        }
      }
    }

    val cycles: ArrayBuffer[Cycle] = ArrayBuffer()

    // handle self-edges first; Johnson's ignores them
    for ((from, _, to) <- edges()) {
      if (to == from)
        cycles += Set(from)
    }

    val sccs = ArrayDeque[Set[Node]]() :++ stronglyConnectedComponents()

    while (!sccs.isEmpty) {
      val component = sccs.removeHead()
      val componentGraph = subgraph(component.toSet)

      val startNode = component.head

      val closed = MSet[Node]()
      val blocked = MSet(startNode)
      var path = List(startNode)

      val noCircuit = MHashMap[Node, MSet[Node]]()

      def neighbourStack(node: Node) = componentGraph(node).filter(node.!=)

      val stack = ArrayBuffer((startNode, neighbourStack(startNode)))

      def scheduleVisitNext(node: Node) = {
        path = node +: path
        ((node, neighbourStack(node))) +=: stack
        closed -= node
        blocked += node
      }

      def tieUpCycle(node: Node) = {
        if (closed contains node) {
          unblock(node, blocked, noCircuit)
        } else {
          for (neighbour <- componentGraph neighbours node) {
            noCircuit.getOrElse(neighbour, MSet[Node]()) += node
          }
        }
        stack.remove(0)

        path = path.tail // Drop thisNode
      }

      while (!stack.isEmpty) {
        // Note: we only pop the stack when we have finished walking all neighbours
        val (thisNode, neighbours) = stack.head
        var thisNodeNextOnStack = true
        if (!neighbours.isEmpty) {
          val nextNode = neighbours.head
          stack(0) = (thisNode, neighbours.tail)

          if (nextNode == startNode) {
            closed ++= path
            cycles += path.toSet

          } else if (!(blocked contains nextNode)) {
            scheduleVisitNext(nextNode)
            thisNodeNextOnStack = false
          }
        }

        if (neighbours.isEmpty && thisNodeNextOnStack) {
          tieUpCycle(thisNode)
        }

      }

      for (component <- (componentGraph subgraph component.tail)
             .stronglyConnectedComponents()
           if component.size > 1) {

        sccs prepend component
      }

    }

    cycles.toSet
  }

  // Create a new homomorphic graph by merging the given nodes, returning both
  // the new graph and the resulting composite node in that graph.
  def mergeNodes(nodesToMerge: Iterable[Node]): CompositeGraph[Node, Label] =
    CompositeGraph(this, nodesToMerge.toSet)

}

class MapGraph[N, L](val underlying: Map[N, List[(N, L)]])
    extends Graphable[N, L] {

  private lazy val nodes: Set[N] = underlying.keySet union underlying.flatMap {
    nodeAndOut =>
      nodeAndOut._2.map(_._1)
  }.toSet

  def this(edges: Iterable[(N, L, N)]) = {
    this(
      edges.map(_._3 -> List()).toMap ++
        edges
          .groupBy(_._1)
          .view
          .mapValues(_.map(v => (v._3, v._2)).toList)
          .toMap
    )
  }

  override def hasNode(node: N) = nodes contains node

  def allNodes() = nodes.toSeq
  def outgoingEdges(node: N) =
    underlying
      .getOrElse(node, Set())
      .map { case (to, label) => (node, label, to) }
      .toSeq
  def subgraph(selectedNodes: Set[N]) =
    new MapGraph[N, L](
      underlying.view
        .filterKeys(selectedNodes contains _)
        .mapValues(nexts => nexts.filter(selectedNodes contains _._1))
        .toMap
    )

  // NOTE: Maintains all nodes
  def dropEdges(edgesToRemove: Set[(N, L, N)]) = {
    val res = MHashMap[N, List[(N, L)]](underlying.toSeq: _*)

    for ((from, label, to) <- edgesToRemove) {
      // TODO this is *not* efficient
      res(from) = res(from).filter((to, label).!=)
    }

    new MapGraph(res.toMap)
  }

  def addEdges(edgesToAdd: Iterable[(N, L, N)]) =
    new MapGraph(this.edges() ++ edgesToAdd)

  def edges() =
    underlying.flatMap { case (v, ws) => ws.map(w => (v, w._2, w._1)) }.toSeq
  override def toString = underlying.toString
}

object MapGraph {
  implicit def mapToLabellessGraph[N](m: Map[N, List[N]]): MapGraph[N, Unit] =
    new MapGraph(m.view.mapValues(_.map(v => (v, ()))).toMap)
  implicit def mapToGraph[N, L](m: Map[N, List[(N, L)]]): MapGraph[N, L] =
    new MapGraph(m)
}

class EdgeWrapper[N, L](val underlying: (N, L, N)) {
  def isSelfEdge() = underlying._1 == underlying._3
  def from() = underlying._1
  def to() = underlying._3
  def label() = underlying._2
}

object EdgeWrapper {
  implicit def tupleToEdgeWrapper[N, L](t: (N, L, N)): EdgeWrapper[N, L] =
    new EdgeWrapper(t)
}

class PathWrapper[N, L](path: Iterable[(N, L, N)]) {
  val underlying = path.toSeq
  def reversePath(): Iterable[(N, L, N)] = underlying.map {
    case (from, label, to) => (to, label, from)
  }
}

object PathWrapper {
  implicit def iterableToEdgeWrapper[N, L](
      t: Iterable[(N, L, N)]
  ): PathWrapper[N, L] =
    new PathWrapper(t)
}

sealed abstract class CompositeNode[N] extends Product with Serializable {
  def representative(): N
}

object CompositeNode {
  final case class MultiNode[N](ns: Iterable[N]) extends CompositeNode[N] {
    val nodes = ns.toSet

    def representative() = nodes.head
  }

  final case class SingleNode[N](node: N) extends CompositeNode[N] {
    def representative() = node
  }
}

object CompositeGraph {
  def apply[N, L](graphToMerge: Graphable[N, L], equivalentNodes: Set[N]) = {
    val mergedClass = new CompositeNode.MultiNode(equivalentNodes)
    val nodeToEqClass: Map[N, CompositeNode[N]] = graphToMerge
      .allNodes()
      .map(
        node =>
          node ->
            (if (equivalentNodes contains node) {
               mergedClass
             } else {
               new CompositeNode.SingleNode(node)
             })
      )
      .toMap

    // Now, merge the redundant edges
    val underlying: Graphable[CompositeNode[N], Set[(N, L, N)]] =
      MapGraph.mapToGraph(
        graphToMerge
          .edges()
          .map {
            case edge @ (from, _, to) =>
              (nodeToEqClass(from), edge, nodeToEqClass(to))
          }
          .groupBy(e => (e.from(), e.to()))
          .map {
            case ((from, to), edgeLump) =>
              (from, edgeLump.map(_.label()).toSet, to)
          }
          .groupBy(_.from())
          .view
          .mapValues(_.map(e => (e.to(), e.label())).toList)
          .toMap
      )

    new CompositeGraph(underlying, nodeToEqClass)
  }

}

// Generate a graph with an equivalence class of nodes merged into one, while
// still preserving identity for transitions, except self-looping edges to/from
// the equivalent nodes. This means that e.g. outgoingEdges(n) might return
// edges not actually starting in n!
class CompositeGraph[N, L](
    private val underlying: Graphable[CompositeNode[N], Set[(N, L, N)]],
    private val nodeToEqClass: Map[N, CompositeNode[N]]
) extends Graphable[CompositeNode[N], Set[(N, L, N)]] {

  implicit def equivalentNode(node: N): CompositeNode[N] = nodeToEqClass(node)

  // FIXME; these should actually return proper CompositeGraph:s
  def addEdges(
      edges: Iterable[(CompositeNode[N], Set[(N, L, N)], CompositeNode[N])]
  ): Graphable[CompositeNode[N], Set[(N, L, N)]] = underlying.addEdges(edges)
  def dropEdges(
      edges: Set[(CompositeNode[N], Set[(N, L, N)], CompositeNode[N])]
  ): Graphable[CompositeNode[N], Set[(N, L, N)]] = underlying.dropEdges(edges)
  def subgraph(
      selectedNodes: Set[CompositeNode[N]]
  ): Graphable[CompositeNode[N], Set[(N, L, N)]] =
    underlying.subgraph(selectedNodes)
  def outgoingEdges(
      node: CompositeNode[N]
  ): Seq[(CompositeNode[N], Set[(N, L, N)], CompositeNode[N])] =
    underlying.outgoingEdges(node)

  def allNodes() = underlying.allNodes()
  def edges() = underlying.edges()

  def flatMergeNodes(nodesToMerge: Iterable[N]): CompositeGraph[N, L] = {
    val newClass = new CompositeNode.MultiNode(nodesToMerge)
    val affectedClasses = newClass.nodes
      .map(this.nodeToEqClass(_))
      .filter(_.isInstanceOf[CompositeNode.MultiNode[N]])
      .toSet

    assert(affectedClasses.isEmpty, "NOT IMPLEMENTED: non-disjoint merging!")

    val nodeToEqClass = this.nodeToEqClass.map {
      // This is safe, because we know we never overlap an equivalence class
      case (node, eqClass: CompositeNode.MultiNode[N]) => (node, eqClass)
      case (node, eqClass: CompositeNode.SingleNode[N]) =>
        node -> (if (newClass.nodes contains eqClass.node) {
                   newClass
                 } else {
                   eqClass
                 })
    }

    // do the standard merging of nodes!

    val underlying: Graphable[CompositeNode[N], Set[(N, L, N)]] =
      MapGraph.mapToGraph(
        this
          .edges()
          .map {
            case (from, label, to) =>
              (
                nodeToEqClass(from.representative()),
                label,
                nodeToEqClass(to.representative())
              )
          }
          .groupBy(e => (e.from(), e.to()))
          .map {
            case ((from, to), edgeLump) =>
              (from, edgeLump.map(_.label()).flatten.toSet, to)
          }
          .groupBy(_.from())
          .view
          .mapValues(_.map(e => (e.to(), e.label())).toList)
          .toMap
      )

    new CompositeGraph(underlying, nodeToEqClass)

  }
}
