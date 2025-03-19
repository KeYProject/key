/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.graph;

import java.util.*;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Triple;

import org.key_project.slicing.DependencyNodeData;
import org.key_project.slicing.DependencyTracker;
import org.key_project.util.EqualsModProofIrrelevancy;
import org.key_project.util.collection.Pair;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The dependency graph tracks the flow of rule applications in the proof tree.
 * Formulas (plus their branch location and polarity) correspond to nodes
 * (see {@link TrackedFormula}).
 * Other kinds of graph nodes exist ({@link ClosedGoal}, {@link AddedRule}, ...).
 * <p>
 * Each proof step defines a hyperedge of the dependency graph.
 * It starts at the inputs used by the rule application and ends at the newly introduced formulas
 * (or other graph nodes).
 * To simplify the implementation, each hyperedge is split into a collection of regular edges.
 * </p>
 *
 * @author Arne Keller
 */
public class DependencyGraph {
    private static final Logger LOGGER = LoggerFactory.getLogger(DependencyGraph.class);

    /**
     * Main storage container of graph nodes and edges.
     */
    private final EquivalenceDirectedGraph graph;
    /**
     * Mapping of rule applications to graph edges.
     * Stores the edges introduced by a proof step.
     */
    private final Map<Node, Collection<AnnotatedEdge>> edgeDataReversed = new IdentityHashMap<>();

    public DependencyGraph() {
        graph = new EquivalenceDirectedGraph();
    }

    private DependencyGraph(DependencyGraph copyFrom) {
        graph = copyFrom.graph.copy();
        graph.edgeSet().forEach(x -> edgeDataReversed
                .computeIfAbsent(x.getProofStep(), _node -> new ArrayList<>()).add(x));
    }

    /**
     * Ensure the provided proof is fully represented in this dependency graph.
     *
     * @param p the proof
     */
    public void ensureProofIsTracked(Proof p) {
        if (!edgeDataReversed.keySet().stream().findFirst().map(x -> x.proof() == p).orElse(true)) {
            throw new IllegalStateException("tried to use DependencyGraph with wrong proof");
        }
        DependencyTracker tracker = p.lookup(DependencyTracker.class);
        var nodeIterator = p.root().subtreeIterator();
        while (nodeIterator.hasNext()) {
            var node = nodeIterator.next();
            if (node.getAppliedRuleApp() == null || edgeDataReversed.containsKey(node)) {
                continue;
            }
            tracker.trackNode(node);
        }
    }

    /**
     * Add a rule application to the dependency graph.
     *
     * @param node the node to add
     * @param input inputs required by this proof step
     *        (pairs of graph node + whether the rule app consumes the node)
     * @param output outputs produced by this proof step
     */
    public void addRuleApplication(Node node, Collection<Pair<GraphNode, Boolean>> input,
            Collection<GraphNode> output) {
        for (Pair<GraphNode, Boolean> in : input) {
            for (GraphNode out : output) {
                AnnotatedEdge edge = new AnnotatedEdge(node, in.second);

                graph.addVertex(in.first);
                graph.addVertex(out);
                graph.addEdge(in.first, out, edge);

                edgeDataReversed.computeIfAbsent(node, n -> new ArrayList<>()).add(edge);
            }
        }
    }

    /**
     * @param node a graph node
     * @return whether the graph contains that node
     */
    public boolean containsNode(GraphNode node) {
        return graph.containsVertex(node);
    }

    /**
     * @param node a graph node
     * @return the rule application(s) that produced the graph node, if any
     */
    public Stream<Node> incomingEdgesOf(GraphNode node) {
        if (!graph.containsVertex(node)) {
            return Stream.of();
        }
        return graph.incomingEdgesOf(node).stream().map(AnnotatedEdge::getProofStep);
    }

    /**
     * @param node a graph node
     * @return the incoming (graph edges, graph sources) of that node
     */
    public Stream<Triple<Node, GraphNode, AnnotatedEdge>> incomingGraphEdgesOf(GraphNode node) {
        if (!graph.containsVertex(node)) {
            return Stream.of();
        }
        return graph.incomingEdgesOf(node).stream()
                .map(edge -> new Triple<>(edge.getProofStep(), graph.getEdgeSource(edge), edge));
    }

    /**
     * @param node a graph node
     * @return the rule application(s) that used the graph node, if any
     */
    public Stream<Node> outgoingEdgesOf(GraphNode node) {
        if (!graph.containsVertex(node)) {
            return Stream.of();
        }
        return graph.outgoingEdgesOf(node).stream().map(AnnotatedEdge::getProofStep);
    }

    /**
     * @param node a graph node
     * @return the outgoing (graph edges, graph targets) of that node
     */
    public Stream<Triple<Node, GraphNode, AnnotatedEdge>> outgoingGraphEdgesOf(GraphNode node) {
        if (!graph.containsVertex(node)) {
            return Stream.of();
        }
        return graph.outgoingEdgesOf(node).stream()
                .map(edge -> new Triple<>(edge.getProofStep(), graph.getEdgeTarget(edge), edge));
    }

    /**
     * @param location branch location
     * @return graph nodes created in that branch (and descendent branches)
     */
    public Stream<GraphNode> nodesInBranch(BranchLocation location) {
        return graph.vertexSet().stream()
                .filter(it -> it.branchLocation.hasPrefix(location));
    }

    /**
     * @param location branch location
     * @return closed goals in that branch and descendents
     */
    public Stream<ClosedGoal> goalsInBranch(BranchLocation location) {
        return graph.vertexSet().stream()
                .filter(ClosedGoal.class::isInstance)
                .map(ClosedGoal.class::cast)
                .filter(it -> it.branchLocation.hasPrefix(location));
    }

    /**
     * @return all nodes contained in the graph
     */
    public Iterable<GraphNode> nodes() {
        return graph.vertexSet();
    }

    /**
     * Process a prune of the proof tree.
     * Deletes graph data that belongs to removed steps.
     *
     * @param pruneTarget the node up to which the prune occurs
     */
    public void prune(Node pruneTarget) {
        // prune event specifies the node pruned to
        // => iterate over all graph edges and check their validity
        // -> remove all vertices added by pruned away steps
        Deque<Node> nodesToProcess = new ArrayDeque<>();
        nodesToProcess.add(pruneTarget);

        Collection<GraphNode> verticesToRemove = new ArrayList<>();
        while (!nodesToProcess.isEmpty()) {
            Node node = nodesToProcess.pop();
            // all children nodes are also pruned
            node.childrenIterator().forEachRemaining(nodesToProcess::add);

            DependencyNodeData data = node.lookup(DependencyNodeData.class);
            if (data != null) {
                verticesToRemove.addAll(data.outputs);
                node.deregister(data, DependencyNodeData.class);
            }
            edgeDataReversed.remove(node);
        }
        graph.removeAllVertices(verticesToRemove);
        LOGGER.debug("After prune: {} nodes, {} edges", graph.vertexSet().size(),
            graph.edgeSet().size());
    }

    /**
     * @param node graph node
     * @return neighbors of that graph node (all nodes connected by incoming or outgoing edge)
     */
    public Stream<GraphNode> neighborsOf(GraphNode node) {
        return Stream.concat(
            graph.incomingEdgesOf(node).stream().map(graph::getEdgeSource),
            graph.outgoingEdgesOf(node).stream().map(graph::getEdgeTarget));
    }

    /**
     * Gets all the edges representing the supplied proof step.
     * The combination of these represents the hyperedge corresponding to the proof step.
     *
     * @param proofStep the proof step
     * @return the edges representing this step
     */
    public Collection<AnnotatedEdge> edgesOf(Node proofStep) {
        return edgeDataReversed.getOrDefault(proofStep, Collections.emptyList());
    }

    /**
     * @param edge a graph edge
     * @return source node of this edge
     */
    public GraphNode inputOf(AnnotatedEdge edge) {
        return graph.getEdgeSource(edge);
    }

    /**
     * @param edge a graph edge
     * @return target node of this edge
     */
    public GraphNode outputOf(AnnotatedEdge edge) {
        return graph.getEdgeTarget(edge);
    }

    /**
     * @param proofStep a proof step
     * @return the graph nodes required by that step
     */
    public Stream<GraphNode> inputsOf(Node proofStep) {
        return edgesOf(proofStep).stream().map(this::inputOf);
    }

    /**
     * @param proofStep a proof step
     * @return the graph nodes created by that step
     */
    public Stream<GraphNode> outputsOf(Node proofStep) {
        return edgesOf(proofStep).stream().map(this::outputOf);
    }

    /**
     * @param proofStep a proof step
     * @return the graph nodes replaced by this proof step (only formulas)
     */
    public Stream<GraphNode> inputsConsumedBy(Node proofStep) {
        return edgesOf(proofStep).stream().filter(AnnotatedEdge::replacesInputNode)
                .map(this::inputOf);
    }

    /**
     * @param node graph node
     * @return the outgoing edges of that node
     */
    public Stream<AnnotatedEdge> edgesUsing(GraphNode node) {
        return outgoingGraphEdgesOf(node).map(it -> it.third);
    }

    /**
     * @param node graph node
     * @return the edge(s) whose proof steps replace this graph node
     */
    public Stream<AnnotatedEdge> edgesConsuming(GraphNode node) {
        return outgoingGraphEdgesOf(node)
                .filter(it -> it.third.replacesInputNode())
                .map(it -> it.third);
    }

    /**
     * @param node graph node
     * @return edges leading to this graph node (proof steps that produced this node)
     */
    public Stream<AnnotatedEdge> edgesProducing(GraphNode node) {
        return incomingGraphEdgesOf(node)
                .map(it -> it.third);
    }

    /**
     * @return number of stored graph nodes
     */
    public int countNodes() {
        return graph.vertexSet().size();
    }

    /**
     * Get the number of edges in this dependency graph.
     * May be larger than the number of represented proof steps, if some proof steps use or produce
     * more than one formula.
     *
     * @return number of stored graph edges
     */
    public int countEdges() {
        return graph.edgeSet().size();
    }

    /**
     * Return the graph node and any previous derivations of it in the same branch.
     *
     * @param node graph node
     * @return passed graph node and equivalent nodes
     */
    public Collection<GraphNode> nodeAndPreviousDerivations(GraphNode node) {
        Collection<GraphNode> all = new ArrayList<>();
        all.add(node);
        if (node instanceof EqualsModProofIrrelevancy) {
            all = graph.getVerticesModProofIrrelevancy(node);
        }
        return all;
    }

    /**
     * Get the graph node of the provided PosInOccurence.
     *
     * @param proof the proof
     * @param locationGuess best guess for the branch the formula was derived in
     *        (allowed to be more specific than the correct branch location)
     * @param pio formula
     * @return graph node, null if not found
     */
    public GraphNode getGraphNode(Proof proof, BranchLocation locationGuess, PosInOccurrence pio) {
        if (proof == null) {
            return null;
        }
        while (true) {
            TrackedFormula formula =
                new TrackedFormula(pio.sequentFormula(), locationGuess, pio.isInAntec(),
                    proof.getServices());
            if (containsNode(formula)) {
                return formula;
            }
            if (locationGuess.isEmpty()) {
                break;
            }
            // remove last branch choice
            locationGuess = locationGuess.removeLast();
        }
        return null;
    }

    /**
     * Remove all nodes B with degree 2:
     * A → B → C
     *
     * @return modified copy
     */
    public DependencyGraph removeChains() {
        // first, create a copy of the graph
        var nGraph = new DependencyGraph(this);
        // get all nodes in the proof
        var allNodes = proof().root().subtreeIterator();
        // take the outputs "produced" by the nodes
        var toCheck = StreamSupport.stream(Spliterators.spliteratorUnknownSize(allNodes, 0), false)
                .flatMap(this::outputsOf).toList();
        int removed = 0;
        // toCheck now contains dependency graph nodes
        // (TrackedFormulas etc.)
        for (var node : toCheck) {
            var incoming = nGraph.incomingGraphEdgesOf(node).toList();
            var outgoing = nGraph.outgoingGraphEdgesOf(node).toList();
            if (incoming.size() != 1 || outgoing.size() != 1) {
                continue;
            }
            // we want to remove the incoming edge.
            // that edge is part of a node startNode,
            // whose hyperedge should not connect more nodes
            // (otherwise we cannot remove the edge without
            // making the graph inconsistent)
            Node startNode = incoming.get(0).first;
            if (edgesOf(startNode).size() != 1) {
                continue;
            }
            GraphNode startGraphNode = incoming.get(0).second;
            AnnotatedEdge edge = incoming.get(0).third;

            // get real initial node
            // (in case of repeated shortenings)
            Node initialNode = startNode;
            if (edge instanceof AnnotatedShortenedEdge ase) {
                initialNode = ase.getInitial();
            }

            // we want to remove the outgoing edge.
            // that edge is part of a node endNode,
            // whose hyperedge should not connect more nodes
            // (otherwise we cannot remove the edge without
            // making the graph inconsistent)
            Node endNode = outgoing.get(0).first;
            GraphNode endGraphNode = outgoing.get(0).second;
            var edge2 = outgoing.get(0).third;
            if (edgesOf(endNode).size() != 1) {
                continue;
            }

            // situation:
            // startGraphNode ---> node ---> endGraphNode

            // chain removal:
            // remove node and connected edges
            nGraph.graph.removeVertex(node);
            // create new edge
            var edge3 = new AnnotatedShortenedEdge(initialNode, endNode, edge.replacesInputNode());
            nGraph.graph.addEdge(startGraphNode, endGraphNode, edge3);
            nGraph.edgeDataReversed.remove(startNode);
            nGraph.edgeDataReversed.get(endNode).remove(edge2);
            nGraph.edgeDataReversed.get(endNode).add(edge3);
            removed++;
        }
        LOGGER.debug("removeChains: {} nodes deleted", removed);
        return nGraph;
    }

    /**
     * The proof associated with this graph. May be null if the graph is empty.
     *
     * @return the proof
     */
    public Proof proof() {
        return this.edgeDataReversed.keySet().stream().map(Node::proof).findFirst().orElse(null);
    }
}
