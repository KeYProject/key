/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check;

import java.util.SortedSet;
import java.util.TreeSet;

/**
 * Represents a vertex/node of a tree.
 *
 * @param <T> the type of the content contained by the node
 * @author Wolfram Pfeifer
 */
public class Node<T extends Comparable<T>> implements Comparable<Node<T>> {
    /** the parent node */
    private final Node<T> parent;

    /** the children nodes */
    private final SortedSet<Node<T>> children = new TreeSet<>();

    /** the content stored in this node */
    private final T content;

    /**
     * Create a new Node with given parent and content.
     *
     * @param parent the parent node
     * @param element the content to store inside this node
     */
    public Node(Node<T> parent, T element) {
        this.parent = parent;
        this.content = element;
    }

    public T getContent() {
        return content;
    }

    public Node<T> getParent() {
        return parent;
    }

    public SortedSet<Node<T>> getChildren() {
        return children;
    }

    /**
     * Adds a node to the set of children.
     *
     * @param child the node to add as a child
     */
    public void addChild(Node<T> child) {
        children.add(child);
    }

    @Override
    public int compareTo(Node<T> o) {
        return content.compareTo(o.content);
    }
}
