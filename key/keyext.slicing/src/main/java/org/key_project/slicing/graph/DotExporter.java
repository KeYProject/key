package org.key_project.slicing.graph;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Pair;
import org.key_project.slicing.AnalysisResults;
import org.key_project.slicing.DependencyNodeData;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Queue;
import java.util.stream.Stream;

/**
 * Exports a {@link DependencyGraph} in DOT format.
 *
 * @author Arne Keller
 */
public final class DotExporter {
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
        buf.append("edge [dir=\"back\"];\n");
        List<Node> queue = new ArrayList<>();
        if (proof.root() != null) { // may be null for proofs with no steps
            queue.add(proof.root());
        }
        while (!queue.isEmpty()) {
            var node = queue.remove(queue.size() - 1);
            node.childrenIterator().forEachRemaining(queue::add);
            var data = node.lookup(DependencyNodeData.class);
            if (data == null) {
                continue;
            }
            for (var in : data.inputs) {
                data.outputs.stream().map(it -> it.toString(abbreviateFormulas, false))
                        .forEach(out -> {
                            buf
                                    .append('"')
                                    .append(in.first.toString(abbreviateFormulas, false))
                                    .append("\" -> \"")
                                    .append(out)
                                    .append("\" [label=\"")
                                    .append(data.label);
                            if (analysisResults != null
                                    && !analysisResults.usefulSteps.contains(node)) {
                                buf.append("\" color=\"red");
                            }
                            buf
                                    .append("\"]\n");
                        });
            }
        }
        if (analysisResults != null) {
            for (var formula : graph.nodes()) {
                if (!analysisResults.usefulNodes.contains(formula)) {
                    buf.append('"').append(formula.toString(abbreviateFormulas, false)).append('"')
                            .append(" [color=\"red\"]\n");
                }
            }
        }
        buf.append("}");
        return buf.toString();
    }

    public static String exportDotAround(
            Proof proof,
            DependencyGraph graph,
            AnalysisResults analysisResults,
            boolean abbreviateFormulas,
            boolean omitBranch,
            GraphNode graphNode) {
        var buf = new StringBuilder();
        buf.append("digraph {\n");
        buf.append("edge [dir=\"back\"];\n");
        var queue = new ArrayList<Pair<GraphNode, Integer>>();
        queue.add(new Pair<>(graphNode, 0));
        var visited = new HashSet<GraphNode>();
        var drawn = new HashSet<Node>();
        while (!queue.isEmpty()) {
            var nodePair = queue.remove(queue.size() - 1);
            if (visited.contains(nodePair.first)) {
                continue;
            }
            var nodeB = nodePair.first;
            visited.add(nodeB);
            var incoming = graph.incomingEdgesOf(nodeB);
            var outgoing = graph.outgoingEdgesOf(nodeB);
            Stream.concat(incoming, outgoing).forEach(node -> {
                if (drawn.contains(node)) {
                    return;
                }
                drawn.add(node);
                var data = node.lookup(DependencyNodeData.class);
                if (data == null) {
                    return;
                }
                for (var in : data.inputs) {
                    for (var out : data.outputs) {
                        var inString = in.first.toString(abbreviateFormulas, omitBranch);
                        var outString = out.toString(abbreviateFormulas, omitBranch);
                        buf
                                .append('"')
                                .append(inString)
                                .append("\" -> \"")
                                .append(outString)
                                .append("\" [label=\"")
                                .append(data.label);
                        if (analysisResults != null
                                && !analysisResults.usefulSteps.contains(node)) {
                            buf.append("\" color=\"red");
                        }
                        buf
                                .append("\"];\n");
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
                    }
                }
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
}
