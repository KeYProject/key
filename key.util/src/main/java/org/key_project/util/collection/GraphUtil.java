/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.function.Function;

import de.uka.ilkd.key.util.Quadruple;

/**
 * Utility functions for manipulating graphs.
 *
 * @author Arne Keller
 */
public final class GraphUtil {
    private GraphUtil() {

    }

    public static <V, E extends DefaultEdge<V>> void collapseChains(DirectedGraph<V, E> graph,
            Function<Quadruple<V, V, E, E>, E> edgeFactory) {
        Deque<V> todo = new ArrayDeque<>(graph.vertexSet());
        while (!todo.isEmpty()) {
            V v = todo.pop();
            var incoming = graph.incomingEdgesOf(v);
            var outgoing = graph.outgoingEdgesOf(v);
            if (incoming.size() == 1 && outgoing.size() == 1) {
                var in = incoming.iterator().next();
                var out = outgoing.iterator().next();
                var newEdge =
                    edgeFactory.apply(new Quadruple<>(in.getSource(), out.getTarget(), in, out));
                var src = in.getSource();
                var dst = out.getTarget();
                graph.removeVertex(v);
                graph.addEdge(src, dst, newEdge);
                todo.add(src);
                todo.add(dst);
            }
        }
    }
}
