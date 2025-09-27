/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check.dependency;

import de.uka.ilkd.key.proof.io.intermediate.NodeIntermediate;

import java.util.Deque;
import java.util.LinkedList;

/**
 * Walks an intermediate proof representation tree as created when loading a *.proof file.
 *
 * @author Jakob Laenge
 * @author Wolfram Pfeifer
 */
public abstract class NodeIntermediateWalker {
    /** the root where the walker starts */
    private final NodeIntermediate root;

    /**
     * create a walker starting from the given root
     *
     * @param root the root of the intermediate proof representation
     */
    protected NodeIntermediateWalker(NodeIntermediate root) {
        this.root = root;
    }

    /** starts the walker */
    public void start() {
        walkIteratively();
    }

    /**
     * Walks the tree while performing specified action.
     *
     * @deprecated Might run into stack overflow for medium to long proofs, use
     * {@link #walkIteratively()} instead.    
     *
     * @param node the current position of the walker in tree
     */
    @Deprecated()
    protected void walkRecursively(NodeIntermediate node) {
        doAction(node);

        for (NodeIntermediate child : node.getChildren()) {
            walkRecursively(child);
        }
    }

    /**
     * Walks the tree while performing specified action. This iterative variant avoids stack
     * overflows and is thus preferred. It performs a breadth-first search traversal.
     */
    protected void walkIteratively () {
        Deque<NodeIntermediate> queue = new LinkedList<>();
        queue.add(root);

        while (!queue.isEmpty()) {
            NodeIntermediate node = queue.pollFirst();
            doAction(node);
            queue.addAll(node.getChildren());
        }
    }

    /**
     * the action to be performed just before leaving the node the last time
     *
     * @param node the current position of the walker
     */
    protected abstract void doAction(NodeIntermediate node);
}
