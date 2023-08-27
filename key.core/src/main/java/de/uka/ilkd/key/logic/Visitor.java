/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

public interface Visitor {
    /**
     * Checks if the subtree below the visited {@link Term} should be traversed.
     *
     * @param visited The currently visited {@link Term}.
     * @return {@code true} visit sub tree, {@code false} skip sub tree.
     */
    boolean visitSubtree(Term visited);

    /**
     * the entry method for the visitor pattern
     *
     * @param visited the Term to be visited
     */
    void visit(Term visited);

    /**
     * this method is called in execPreOrder and execPostOrder in class Term when entering the
     * subtree rooted in the term subtreeRoot. Default implementation is to do nothing. Subclasses
     * can override this method when the visitor behaviour depends on informations bound to
     * subtrees.
     *
     * @param subtreeRoot root of the subtree which the visitor enters.
     */

    void subtreeEntered(Term subtreeRoot);

    /**
     * this method is called in execPreOrder and execPostOrder in class Term when leaving the
     * subtree rooted in the term subtreeRoot. Default implementation is to do nothing. Subclasses
     * can override this method when the visitor behaviour depends on informations bound to
     * subtrees.
     *
     * @param subtreeRoot root of the subtree which the visitor leaves.
     */

    void subtreeLeft(Term subtreeRoot);
}
