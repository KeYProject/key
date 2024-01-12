/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Simple implementation of the {@link Graph} interface.
 *
 * @param <V> vertex type
 * @param <E> edge type
 * @author Arne Keller
 */
public class DirectedGraph<V, E extends GraphEdge> implements Graph<V, E> {
    /**
     * Set of vertices in this graph.
     */
    private final Set<V> vertices = new HashSet<>();
    /**
     * For each vertex: edges leading to that vertex. May be null if no such edge has been added.
     */
    private final Map<V, Set<E>> incomingEdges = new HashMap<>();
    /**
     * For each vertex: edges starting at that vertex. May be null if no such edge has been added.
     */
    private final Map<V, Set<E>> outgoingEdges = new HashMap<>();
    /**
     * Set of edges in this graph.
     */
    private final Set<E> edges = new HashSet<>();

    @Override
    public boolean addVertex(V v) {
        if (vertices.contains(v)) {
            return false;
        }
        vertices.add(v);
        return true;
    }

    @Override
    public void addEdge(V source, V target, E edge) {
        addVertex(source);
        addVertex(target);
        edges.add(edge);
        edge.setSource(source);
        edge.setTarget(target);
        outgoingEdges.computeIfAbsent(source, _source -> new HashSet<>()).add(edge);
        incomingEdges.computeIfAbsent(target, _target -> new HashSet<>()).add(edge);
    }

    @Override
    public boolean containsVertex(V v) {
        return vertices.contains(v);
    }

    @Override
    public Collection<E> incomingEdgesOf(V v) {
        if (!incomingEdges.containsKey(v)) {
            return Collections.emptySet();
        }
        return Collections.unmodifiableSet(incomingEdges.get(v));
    }

    @Override
    public Collection<E> outgoingEdgesOf(V v) {
        if (!outgoingEdges.containsKey(v)) {
            return Collections.emptySet();
        }
        return Collections.unmodifiableSet(outgoingEdges.get(v));
    }

    @Override
    public V getEdgeSource(E edge) {
        return (V) edge.getSource();
    }

    @Override
    public V getEdgeTarget(E edge) {
        return (V) edge.getTarget();
    }

    @Override
    public Set<V> vertexSet() {
        return Collections.unmodifiableSet(vertices);
    }

    @Override
    public Set<E> edgeSet() {
        return Collections.unmodifiableSet(edges);
    }

    @Override
    public void removeAllVertices(Collection<V> vertices) {
        vertices.forEach(this::removeVertex);
    }

    @Override
    public void removeVertex(V v) {
        Set<E> incoming = incomingEdges.get(v);
        if (incoming != null) {
            incoming.forEach(e -> {
                edges.remove(e);
                outgoingEdges.get(e.getSource()).remove(e);
            });
            incomingEdges.remove(v);
        }
        Set<E> outgoing = outgoingEdges.get(v);
        if (outgoing != null) {
            outgoing.forEach(e -> {
                edges.remove(e);
                incomingEdges.get(e.getTarget()).remove(e);
            });
            outgoingEdges.remove(v);
        }
        vertices.remove(v);
        incomingEdges.remove(v);
        outgoingEdges.remove(v);
    }

    @Override
    public void removeEdge(E e) {
        outgoingEdges.get(e.getSource()).remove(e);
        incomingEdges.get(e.getTarget()).remove(e);
        edges.remove(e);
    }
}
