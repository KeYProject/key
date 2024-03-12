/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.SourceElement;

/**
 * This interface is used to walk a tree of {@link SourceElement}s. The tree is
 * traversed in depth-first order, and the walker can be used to visit the
 * children of a node, the siblings of a node and the parent of a node.
 */
public interface TreeWalker {
    /**
     * Returns the root of the tree that is being walked.
     *
     * @return the root of the tree that is being walked
     */
    SourceElement getRoot();

    /**
     * Returns the node of the tree the walker is currently at.
     *
     * @return the node of the tree the walker is currently at
     */
    SourceElement getCurrentNode();

    /**
     * Returns the first child of the current node, or {@code null} if the
     * current node has no children.
     *
     * @return the first child of the current node, or {@code null} if the
     *         current node has no children
     */
    SourceElement firstChild();

    /**
     * Returns the last child of the current node, or {@code null} if the current
     * node has no children.
     *
     * @return the last child of the current node, or {@code null} if the current
     *         node has no children
     */
    SourceElement lastChild();

    /**
     * Returns the next node in the tree, or {@code null} if the current node is
     * the last node in the tree.
     *
     * @return the next node in the tree, or {@code null} if the current node is
     *         the last node in the tree
     */
    SourceElement nextNode();

    SourceElement previousNode();

    /**
     * Returns the next sibling of the current node, or {@code null} if the current
     * node has no next sibling.
     *
     * @return the next sibling of the current node, or {@code null} if the current
     *         node has no next sibling
     */
    SourceElement nextSibling();

    /**
     * Returns the previous sibling of the current node, or {@code null} if the
     * current node has no previous sibling.
     *
     * @return the previous sibling of the current node, or {@code null} if the
     *         current node has no previous sibling
     */
    SourceElement previousSibling();

    /**
     * Returns the parent of the current node, or {@code null} if the current node
     * has no parent.
     *
     * @return the parent of the current node, or {@code null} if the current node
     *         has no parent
     */
    SourceElement parentNode();
}
