/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class TestDirectedGraph {
    private final static String VERTEX_1 = "v1";
    private final static String VERTEX_2 = "v2";
    private final static String VERTEX_3 = "v3";
    private final static String VERTEX_4 = "v4";

    @Test
    void insertAndRemove() {
        Graph<String, DefaultEdge> graph = new DirectedGraph<>();
        graph.addVertex(VERTEX_1);
        graph.addVertex(VERTEX_2);
        graph.addVertex(VERTEX_3);
        assertEquals(3, graph.vertexSet().size());
        graph.removeVertex(VERTEX_1);
        assertEquals(2, graph.vertexSet().size());
        assertTrue(graph.vertexSet().contains(VERTEX_2));
        assertTrue(graph.vertexSet().contains(VERTEX_3));

        graph.addEdge(VERTEX_1, VERTEX_2, new DefaultEdge());
        assertEquals(3, graph.vertexSet().size());
        assertEquals(1, graph.edgeSet().size());
        assertEquals(1, graph.outgoingEdgesOf(VERTEX_1).size());
        assertEquals(1, graph.incomingEdgesOf(VERTEX_2).size());
        assertEquals(0, graph.outgoingEdgesOf(VERTEX_2).size());
        assertEquals(0, graph.incomingEdgesOf(VERTEX_1).size());

        DefaultEdge e = graph.edgeSet().iterator().next();
        assertEquals(VERTEX_1, e.getSource());
        assertEquals(VERTEX_1, graph.getEdgeSource(e));
        assertEquals(VERTEX_2, e.getTarget());
        assertEquals(VERTEX_2, graph.getEdgeTarget(e));

        graph.removeVertex(VERTEX_1);
        assertEquals(2, graph.vertexSet().size());
        assertEquals(0, graph.edgeSet().size());
        assertEquals(0, graph.outgoingEdgesOf(VERTEX_1).size());
        assertEquals(0, graph.incomingEdgesOf(VERTEX_2).size());
        assertEquals(0, graph.outgoingEdgesOf(VERTEX_2).size());
        assertEquals(0, graph.incomingEdgesOf(VERTEX_1).size());

        graph.removeAllVertices(List.of(VERTEX_2, VERTEX_3));
        assertEquals(0, graph.vertexSet().size());
    }

    @Test
    void insertAndRemoveEdges() {
        Graph<String, GraphEdge> graph = new DirectedGraph<>();
        graph.addVertex(VERTEX_1);
        graph.addVertex(VERTEX_2);
        graph.addVertex(VERTEX_3);
        graph.addVertex(VERTEX_4);

        graph.addEdge(VERTEX_1, VERTEX_2, new DefaultEdge());
        // loops are allowed
        graph.addEdge(VERTEX_2, VERTEX_2, new DefaultEdge());
        GraphEdge e23 = new DefaultEdge();
        graph.addEdge(VERTEX_2, VERTEX_3, e23);
        GraphEdge e24 = new DefaultEdge();
        graph.addEdge(VERTEX_2, VERTEX_4, e24);
        assertEquals(4, graph.vertexSet().size());
        assertEquals(4, graph.edgeSet().size());

        assertEquals(1, graph.outgoingEdgesOf(VERTEX_1).size());
        assertEquals(0, graph.incomingEdgesOf(VERTEX_1).size());
        assertEquals(3, graph.outgoingEdgesOf(VERTEX_2).size());
        assertEquals(2, graph.incomingEdgesOf(VERTEX_2).size());
        assertEquals(VERTEX_2, e24.getSource());
        assertEquals(VERTEX_4, e24.getTarget());

        graph.removeEdge(e24);
        assertEquals(3, graph.edgeSet().size());
        assertEquals(0, graph.incomingEdgesOf(VERTEX_4).size());
        assertEquals(2, graph.outgoingEdgesOf(VERTEX_2).size());

        graph.addEdge(VERTEX_1, VERTEX_4, e24);
        assertEquals(4, graph.edgeSet().size());
        assertEquals(1, graph.incomingEdgesOf(VERTEX_4).size());
        assertEquals(2, graph.outgoingEdgesOf(VERTEX_2).size());
        assertEquals(2, graph.outgoingEdgesOf(VERTEX_1).size());
        assertEquals(VERTEX_1, e24.getSource());
        assertEquals(VERTEX_4, e24.getTarget());

        graph.removeAllVertices(List.of(VERTEX_2, VERTEX_3));
        assertEquals(1, graph.edgeSet().size());
    }
}
