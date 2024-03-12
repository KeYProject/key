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
     * Walks to the first child of the current node, or stays in place if the current node has no
     * children.
     *
     * @return the first child of the current node, or {@code null} if the current node has no
     *         children
     */
    SourceElement firstChild();

    /**
     * Walks to the last child of the current node, or stays in place if the current node has no
     * children.
     *
     * @return the last child of the current node, or {@code null} if the current node has no
     *         children
     */
    SourceElement lastChild();

    /**
     * Walks to the next node in the tree, or stays in place if the current node is the last node in
     * the tree.
     * <p>
     * Possible candidates for the next node are (in this order):
     * <p>
     * 1. The first child of the current node
     * <p>
     * 2. The next sibling of the current node
     * <p>
     * 3. The first found next sibling of some ancestor of the current node from bottom to top
     *
     * @return the next node in the tree, or {@code null} if the current node is the last node in
     *         the tree
     */
    SourceElement nextNode();

    /**
     * Walks to the previous node in the tree, or stays in place if the current node is the first
     * node in the tree.
     * <p>
     * Possible candidates for the previous node are (in this order):
     * <p>
     * 1. The furthest down last descendant of the previous sibling of the current node in the tree
     * <p>
     * 2. The previous sibling of the current node
     * <p>
     * 3. The parent of the current node
     *
     * @return the previous node in the tree, or {@code null} if the current node is the last node
     *         in the tree
     */
    SourceElement previousNode();

    /**
     * Walks to the next sibling of the current node, or stays in place if the current node has no
     * next sibling.
     *
     * @return the next sibling of the current node, or {@code null} if the current node has no next
     *         sibling
     */
    SourceElement nextSibling();

    /**
     * Walks to the previous sibling of the current node, or stays in place if the current node has
     * no previous sibling.
     *
     * @return the previous sibling of the current node, or {@code null} if the current node has no
     *         previous sibling
     */
    SourceElement previousSibling();

    /**
     * Walks to the parent of the current node, or stays in place if the current node has no parent.
     *
     * @return the parent of the current node, or {@code null} if the current node
     *         has no parent
     */
    SourceElement parentNode();
}
