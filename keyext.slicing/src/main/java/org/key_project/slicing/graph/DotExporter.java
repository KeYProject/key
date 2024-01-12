/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.graph;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Pair;

import org.key_project.slicing.DependencyNodeData;
import org.key_project.slicing.analysis.AnalysisResults;

/**
 * Exports a {@link DependencyGraph} in DOT format.
 *
 * @author Arne Keller
 */
public final class DotExporter {
    /**
     * Overrides node shape for specified classes of graph nodes.
     */
    private static final Map<Class<? extends GraphNode>, String> SHAPES = new IdentityHashMap<>();
    static {
        SHAPES.put(ClosedGoal.class, "rectangle");
    }

    private DotExporter() {
    }

    /**
     * Convert the given dependency graph into a text representation (DOT format).
     * If analysis results are given, useless nodes and edges are marked in red.
     * If <code>abbreviateFormulas</code> is true, node labels are shortened.
     *
     * @param proof proof to export
     * @param graph dependency graph to show
     * @param analysisResults analysis results (may be null)
     * @param abbreviateFormulas whether node labels should be shortened
     * @return string representing the dependency graph
     */
    public static String exportDot(
            Proof proof,
            DependencyGraph graph,
            AnalysisResults analysisResults,
            boolean abbreviateFormulas) {
        StringBuilder buf = new StringBuilder();
        buf.append("digraph {\n");
        // expected direction in output rendering is reverse internal order
        buf.append("edge [dir=\"back\"];\n");

        // output each edge of the dependency graph
        List<Node> queue = new ArrayList<>();
        if (proof.root() != null) { // may be null for proofs with no steps
            queue.add(proof.root());
        }
        while (!queue.isEmpty()) {
            Node node = queue.remove(queue.size() - 1);
            node.childrenIterator().forEachRemaining(queue::add);
            DependencyNodeData data = node.lookup(DependencyNodeData.class);
            if (data == null) {
                continue;
            }
            outputEdge(buf, analysisResults, abbreviateFormulas, false, node, data);
        }
        // colorize useless nodes
        if (analysisResults != null) {
            for (GraphNode formula : graph.nodes()) {
                if (!analysisResults.usefulNodes.contains(formula)) {
                    buf.append('"').append(formula.toString(abbreviateFormulas, false)).append('"')
                            .append(" [color=\"red\"]\n");
                }
            }
        }
        buf.append("}");
        return buf.toString();
    }

    /**
     * Export the graph around a specific node.
     *
     * @param graph graph
     * @param analysisResults analysis results
     * @param abbreviateFormulas whether to abbreviate node labels
     * @param omitBranch whether to omit branch information
     * @param graphNode the graph node to export a drawing around
     * @return DOT string of the nodes and edges around {@code graphNode}
     */
    public static String exportDotAround(
            DependencyGraph graph,
            AnalysisResults analysisResults,
            boolean abbreviateFormulas,
            boolean omitBranch,
            GraphNode graphNode) {
        StringBuilder buf = new StringBuilder();
        buf.append("digraph {\n");
        buf.append("edge [dir=\"back\"];\n");
        // queue of: (graph node, depth required to find graph node)
        List<Pair<GraphNode, Integer>> queue = new ArrayList<>();
        queue.add(new Pair<>(graphNode, 0));

        Set<GraphNode> visited = new HashSet<>();
        Set<Node> drawn = new HashSet<>();
        while (!queue.isEmpty()) {
            Pair<GraphNode, Integer> nodePair = queue.remove(queue.size() - 1);
            if (visited.contains(nodePair.first)) {
                continue;
            }
            GraphNode nodeB = nodePair.first;
            visited.add(nodeB);
            Stream<Node> incoming = graph.incomingEdgesOf(nodeB);
            Stream<Node> outgoing = graph.outgoingEdgesOf(nodeB);
            Stream.concat(incoming, outgoing).forEach(node -> {
                if (drawn.contains(node)) {
                    return;
                }
                drawn.add(node);
                DependencyNodeData data = node.lookup(DependencyNodeData.class);
                if (data == null) {
                    return;
                }
                outputEdge(buf, analysisResults, abbreviateFormulas, omitBranch, node, data);
            });
            if (nodePair.second < 1) {
                graph.neighborsOf(nodeB)
                        .forEach(newNode -> queue.add(new Pair<>(newNode, nodePair.second + 1)));
            }
        }
        buf.append('"').append(graphNode.toString(abbreviateFormulas, omitBranch))
                .append("\" [fontsize=\"28pt\"];");
        buf.append('}');
        return buf.toString();
    }

    /**
     * Write a single edge to the provided string builder.
     * This will emit an edge between every input and output of the provided node.
     * It will also style the formula nodes using the shapes specified in {@link #SHAPES}.
     *
     * @param buf output buffer
     * @param analysisResults analysis results (if available)
     * @param abbreviateFormulas whether to shorten node labels
     * @param omitBranch whether to omit branch labels
     * @param node the node to describe
     * @param data dependency graph data on the node
     */
    private static void outputEdge(StringBuilder buf, AnalysisResults analysisResults,
            boolean abbreviateFormulas, boolean omitBranch, Node node, DependencyNodeData data) {
        for (Pair<GraphNode, Boolean> in : data.inputs) {
            String inString = in.first.toString(abbreviateFormulas, omitBranch);
            for (GraphNode out : data.outputs) {
                String outString = out.toString(abbreviateFormulas, omitBranch);
                buf
                        .append('"')
                        .append(inString)
                        .append("\" -> \"")
                        .append(outString)
                        .append("\" [label=\"")
                        .append(data.label);
                // mark useless steps / formulas in red
                if (analysisResults != null
                        && !analysisResults.usefulSteps.contains(node)) {
                    buf.append("\" color=\"red");
                }
                buf
                        .append("\"]\n");
                if (analysisResults != null) {
                    if (!analysisResults.usefulNodes.contains(in.first)) {
                        buf.append('"').append(inString).append('"')
                                .append(" [color=\"red\"]\n");
                    }
                    if (!analysisResults.usefulNodes.contains(out)) {
                        buf.append('"').append(outString).append('"')
                                .append(" [color=\"red\"]\n");
                    }
                }
                // make sure the formulas are drawn with the correct shape
                String shape = SHAPES.get(in.first.getClass());
                if (shape != null) {
                    buf.append('"').append(inString).append("\" [shape=\"").append(shape)
                            .append("\"]\n");
                }
                shape = SHAPES.get(out.getClass());
                if (shape != null) {
                    buf.append('"').append(outString).append("\" [shape=\"").append(shape)
                            .append("\"]\n");
                }
            }
        }
    }
}
