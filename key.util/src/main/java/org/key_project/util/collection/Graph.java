/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.Collection;
import java.util.Set;

/**
 * A graph object <code>G(V,E)</code> contains a set <code>V</code> of vertices and a set <code>
 * E</code> of edges. Each edge e=(v1,v2) in E connects source vertex v1 to target vertex v2.
 * For more information about graphs and their related definitions see
 * <a href="http://mathworld.wolfram.com/Graph.html">Wolfram MathWorld</a>.
 *
 * @param <V> the graph vertex type
 * @param <E> the graph edge type
 *
 * @author Arne Keller
 */
public interface Graph<V, E> {
    /**
     * Adds the specified vertex to this graph if not already present.
     *
     * @param v vertex to be added to this graph.
     *
     * @return <code>true</code> if this graph did not already contain the specified vertex.
     *
     * @throws NullPointerException if the specified vertex is <code>null</code>.
     */
    boolean addVertex(V v);

    /**
     * Add an edge to this graph.
     *
     * @param source source vertex
     * @param target target vertex
     * @param edge edge
     */
    void addEdge(V source, V target, E edge);

    /**
     * @param v vertex to search for
     * @return whether that vertex is in the graph
     */
    boolean containsVertex(V v);

    /**
     * @param v vertex
     * @return incoming edges of v (edges that have v as target)
     */
    Collection<E> incomingEdgesOf(V v);

    /**
     * @param v vertex
     * @return outgoing edges of v (edges that have v as source)
     */
    Collection<E> outgoingEdgesOf(V v);

    /**
     * @param edge edge
     * @return source vertex of this edge
     */
    V getEdgeSource(E edge);

    /**
     * @param edge edge
     * @return target vertex of this edge
     */
    V getEdgeTarget(E edge);

    /**
     * @return collection of vertices in this graph (updated as the graph changes)
     */
    Set<V> vertexSet();

    /**
     * @return collection of edges in this graph
     */
    Set<E> edgeSet();

    /**
     * Removes all specified vertices from this graph.
     * Attached edges are also removed.
     *
     * @param vertices vertices to remove
     */
    void removeAllVertices(Collection<V> vertices);

    /**
     * Remove a vertex and all associated edges.
     *
     * @param v vertex to remove
     */
    void removeVertex(V v);

    /**
     * Remove an edge.
     *
     * @param e edge to remove
     */
    void removeEdge(E e);

}
