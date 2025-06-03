/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.graph;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.EqualsAndHashCodeDelegator;
import org.key_project.util.collection.DirectedGraph;

/**
 * A directed graph, extended to store equivalence groups of vertices.
 * Equivalence groups are identified using equality modulo proof irrelevancy.
 * These groups are used to find multiple instances of the same formula in the graph.
 *
 * @author Arne Keller
 */
public class EquivalenceDirectedGraph extends DirectedGraph<GraphNode, AnnotatedEdge> {
    /**
     * Vertices in this graph, grouped using equality modulo proof irrelevancy.
     */
    private final Map<EqualsAndHashCodeDelegator<?>, Collection<GraphNode>> verticesModProof =
        new HashMap<>();

    @Override
    public boolean addVertex(GraphNode v) {
        if (super.addVertex(v)) {
            if (v instanceof TrackedFormula tf) {
                verticesModProof.computeIfAbsent(
                    new EqualsAndHashCodeDelegator<>(tf,
                        TrackedFormula::equalsModProofIrrelevancy,
                        TrackedFormula::hashCodeModProofIrrelevancy),
                    _v -> new ArrayList<>()).add(v);
            }
            return true;
        }
        return false;
    }

    @Override
    public void removeVertex(GraphNode v) {
        super.removeVertex(v);
        if (v instanceof TrackedFormula tf) {
            EqualsAndHashCodeDelegator<?> wrapper =
                new EqualsAndHashCodeDelegator<>(tf,
                    (t1, t2) -> t1.equalsModProofIrrelevancy(t2),
                    t -> t.hashCodeModProofIrrelevancy());
            Collection<GraphNode> group = verticesModProof.get(wrapper);
            group.remove(v);
            if (group.isEmpty()) {
                verticesModProof.remove(wrapper);
            }
        }
    }

    /**
     * @param v vertex to search for
     * @return all vertices in the graph equal to the parameter modulo proof irrelevancy.
     */
    public Collection<GraphNode> getVerticesModProofIrrelevancy(GraphNode v) {
        if (v instanceof TrackedFormula tf) {
            return verticesModProof
                    .get(new EqualsAndHashCodeDelegator<>(tf,
                        TrackedFormula::equalsModProofIrrelevancy,
                        TrackedFormula::hashCodeModProofIrrelevancy));
        } else {
            return List.of(v);
        }
    }

    public EquivalenceDirectedGraph copy() {
        var g = new EquivalenceDirectedGraph();
        for (var vertex : vertexSet()) {
            g.addVertex(vertex);
        }
        for (var edge : edgeSet()) {
            g.addEdge((GraphNode) edge.getSource(), (GraphNode) edge.getTarget(), edge);
        }
        return g;
    }
}
