/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

/**
 * Directed graph edge for use in {@link DirectedGraph} that simply stores the source and target
 * graph nodes.
 *
 * @author Arne Keller
 */
public class DefaultEdge<V> implements GraphEdge<V> {
    /**
     * Source node of this edge.
     */
    private V source;
    /**
     * Target node of this edge.
     */
    private V target;

    @Override
    public V getSource() {
        return source;
    }

    @Override
    public void setSource(V source) {
        this.source = source;
    }

    @Override
    public V getTarget() {
        return target;
    }

    @Override
    public void setTarget(V target) {
        this.target = target;
    }
}
