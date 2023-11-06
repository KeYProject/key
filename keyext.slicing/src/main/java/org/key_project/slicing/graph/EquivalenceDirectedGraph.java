/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.graph;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.EqualsModProofIrrelevancy;
import org.key_project.util.EqualsModProofIrrelevancyWrapper;
import org.key_project.util.collection.DirectedGraph;

/**
 * A directed graph, extended to store equivalence groups of vertices.
 * Equivalence groups are identified using {@link EqualsModProofIrrelevancy}.
 * These groups are used to find multiple instances of the same formula in the graph.
 *
 * @author Arne Keller
 */
public class EquivalenceDirectedGraph extends DirectedGraph<GraphNode, AnnotatedEdge> {
    /**
     * Vertices in this graph, grouped using {@link org.key_project.util.EqualsModProofIrrelevancy}.
     */
    private final Map<EqualsModProofIrrelevancyWrapper<?>, Collection<GraphNode>> verticesModProof =
        new HashMap<>();

    @Override
    public boolean addVertex(GraphNode v) {
        if (super.addVertex(v)) {
            if (v instanceof EqualsModProofIrrelevancy) {
                verticesModProof.computeIfAbsent(
                    new EqualsModProofIrrelevancyWrapper<>((EqualsModProofIrrelevancy) v),
                    _v -> new ArrayList<>()).add(v);
            }
            return true;
        }
        return false;
    }

    @Override
    public void removeVertex(GraphNode v) {
        super.removeVertex(v);
        if (v instanceof EqualsModProofIrrelevancy) {
            EqualsModProofIrrelevancyWrapper<?> wrapper =
                new EqualsModProofIrrelevancyWrapper<>((EqualsModProofIrrelevancy) v);
            Collection<GraphNode> group = verticesModProof.get(wrapper);
            group.remove(v);
            if (group.isEmpty()) {
                verticesModProof.remove(wrapper);
            }
        }
    }

    /**
     * @param v vertex to search for
     * @return all vertices in the graph equal to the parameter
     *         (according to {@link org.key_project.util.EqualsModProofIrrelevancy})
     */
    public Collection<GraphNode> getVerticesModProofIrrelevancy(GraphNode v) {
        if (v instanceof EqualsModProofIrrelevancy) {
            return verticesModProof
                    .get(new EqualsModProofIrrelevancyWrapper<>((EqualsModProofIrrelevancy) v));
        } else {
            return List.of(v);
        }
    }
}
