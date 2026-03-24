/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check.dependency;

import de.uka.ilkd.key.proof.io.intermediate.NodeIntermediate;

/**
 * Walks an intermediate proof representation tree as created when loading a *.proof file.
 *
 * @author Jakob Laenge
 * @author Wolfram Pfeifer
 */
public abstract class NodeIntermediateWalker {
    /** the root where the walker starts */
    private NodeIntermediate root;

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
        walk(root);
    }

    /**
     * walks the tree while performing specified action
     *
     * @param node the current position of the walker in tree
     */
    protected void walk(NodeIntermediate node) {
        doAction(node);

        // Optimization: for the common case of a single child node,
        // avoid recursion (prevents stack overflow for large proof)
        var children = node.getChildren();
        while (children.size() == 1) {
            var nextNode = children.getFirst();
            doAction(nextNode);
            children = nextNode.getChildren();
        }

        for (NodeIntermediate child : children) {
            walk(child);
        }
    }

    /**
     * the action to be performed just before leaving the node the last time
     *
     * @param node the current position of the walker
     */
    protected abstract void doAction(NodeIntermediate node);
}
