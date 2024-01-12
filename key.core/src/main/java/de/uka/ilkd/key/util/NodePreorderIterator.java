/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import de.uka.ilkd.key.proof.Node;

/**
 * <p>
 * Iterates preorder over the whole sub tree of a given {@link Node}.
 * </p>
 * <p>
 * Instances of this class should always be used instead of recursive method calls because they
 * cause {@link StackOverflowError}s even in small programs.
 * </p>
 * <p>
 * <b>Attention: </b>The iteration process does not take care of changes in the model. If the
 * containment hierarchy changes during iteration it is possible that elements are left or visited
 * multiple times. For this reason it is forbidden to change the model during iteration. But the
 * developer has to take care about it.
 * </p>
 *
 * @author Martin Hentschel
 */
public class NodePreorderIterator {
    /**
     * The element at that the iteration has started used as end condition to make sure that only
     * over the subtree of the element is iterated.
     */
    private final Node start;

    /**
     * The next element or {@code null} if no more elements exists.
     */
    private Node next;

    /**
     * The child index of {@link #next} on its parent.
     */
    private int childIndexOnParent;

    /**
     * The number of previously returned parents.
     */
    private int returnedParents;

    /**
     * Constructor.
     *
     * @param start The {@link Node} to iterate over its sub tree.
     */
    public NodePreorderIterator(Node start) {
        this.start = start;
        this.next = start;
        this.returnedParents = 0;
        if (start != null) {
            Node parent = start.parent();
            if (parent != null) {
                this.childIndexOnParent = parent.getChildNr(start);
            } else {
                this.childIndexOnParent = -1;
            }
        } else {
            this.childIndexOnParent = -1;
        }
    }

    /**
     * Checks if more elements are available.
     *
     * @return {@code true} has more elements, {@code false} has not more elements.
     */
    public boolean hasNext() {
        return next != null;
    }

    /**
     * Returns the next {@link Node} in the containment hierarchy.
     *
     * @return The next {@link Node}.
     */
    public Node next() {
        Node oldNext = next;
        updateNext();
        return oldNext;
    }

    /**
     * Returns the child index of {@link #next()} on its parent.
     * <p>
     * <b>Attention:</b> Needs to be called before {@link #next()} is called.
     *
     * @return The child index of {@link #next()} on its parent or {@code -1} if no parent is
     *         available.
     */
    public int getChildIndexOnParent() {
        return childIndexOnParent;
    }

    /**
     * Returns the number of returned parent after the previous {@link #next()} call which where
     * required in order to find the next {@link Node} which will be returned by the next call of
     * {@link #next()}.
     *
     * @return The number of returned parents.
     */
    public int getReturnedParents() {
        return returnedParents;
    }

    /**
     * Computes the next element and updates {@link #next()}.
     */
    protected void updateNext() {
        Node newNext = null;
        if (next.childrenCount() >= 1) {
            this.childIndexOnParent = 0;
            this.returnedParents = 0;
            newNext = next.child(0);
        } else {
            this.returnedParents = 1;
            newNext = getNextOnParent(next);
        }
        this.next = newNext;
    }

    /**
     * Returns the next element to select if all children of the given {@link Node} are visited.
     *
     * @param node The visited {@link Node}.
     * @return The next {@link Node} to visit.
     */
    protected Node getNextOnParent(Node node) {
        Node parent = node.parent();
        while (parent != null) {
            boolean nodeFound = false; // Indicates that node was found on the parent.
            Node nextChildOnParent = null; // The next child on the parent or the last child after
                                           // iteration has finished
            for (int i = 0; i < parent.childrenCount(); i++) {
                nextChildOnParent = parent.child(i);
                if (nextChildOnParent == start) {
                    childIndexOnParent = -1;
                    return null;
                }
                if (nodeFound) {
                    childIndexOnParent = i;
                    return nextChildOnParent;
                }
                if (nextChildOnParent == node) {
                    nodeFound = true;
                }
            }
            if (nextChildOnParent != start) {
                node = parent; // Continue search on parent without recursive call!
                parent = parent.parent();
                returnedParents++;
            } else {
                childIndexOnParent = -1;
                return null;
            }
        }
        childIndexOnParent = -1;
        return null; // No more parents available.
    }
}
