/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.intermediate;

import java.util.ArrayDeque;
import java.util.LinkedList;
import java.util.Queue;

/**
 * Node in an intermediate proof representation. Responsible for storing information about children
 * of nodes.
 *
 * @author Dominic Scheurer
 */
public abstract class NodeIntermediate {

    /**
     * Children nodes of this node.
     */
    private LinkedList<NodeIntermediate> children = new LinkedList<>();
    /**
     * Number of nodes in the node tree rooted at this object.
     * Cached value, computed on first request.
     */
    private int subtreeSize = -1;

    public LinkedList<NodeIntermediate> getChildren() {
        return children;
    }

    public void setChildren(LinkedList<NodeIntermediate> children) {
        this.children = children;
        this.subtreeSize = -1;
    }

    public void addChild(NodeIntermediate child) {
        this.children.add(child);
        this.subtreeSize = -1;
    }

    /**
     * @return number of NodeIntermediates in this tree of nodes (including this node)
     */
    public int countAllChildren() {
        if (subtreeSize != -1) {
            return subtreeSize;
        }
        int total = 1;
        Queue<NodeIntermediate> queue = new ArrayDeque<>(getChildren());
        while (!queue.isEmpty()) {
            total++;
            queue.addAll(queue.poll().getChildren());
        }
        subtreeSize = total;
        return total;
    }
}
