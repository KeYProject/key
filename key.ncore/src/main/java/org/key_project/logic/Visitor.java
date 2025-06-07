/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;


public interface Visitor<T extends Term> {
    ///
    /// Checks if the subtree below the visited [Term] should be traversed.
    ///
    ///
    /// By default, it always accepts any tree
    ///
    ///
    /// @param visited The currently visited [Term].
    /// @return `true` visit subtree, `false` skip sub tree.
    default boolean visitSubtree(T visited) {
        return true;
    }

    /// the entry method for the visitor pattern
    ///
    /// @param visited the Term to be visited
    void visit(T visited);

    /// this method is called in execPreOrder and execPostOrder in class Term when entering the
    /// subtree rooted in the term subtreeRoot. Default implementation is to do nothing. Subclasses
    /// can override this method when the visitor behaviour depends on informations bound to
    /// subtrees.
    ///
    /// By default, it does nothing
    ///
    ///
    /// @param subtreeRoot root of the subtree which the visitor enters.
    default void subtreeEntered(T subtreeRoot) {
        // do nothing
    }

    /// this method is called in execPreOrder and execPostOrder in class Term when leaving the
    /// subtree rooted in the term subtreeRoot. Default implementation is to do nothing. Subclasses
    /// can override this method when the visitor behaviour depends on informations bound to
    /// subtrees.
    ///
    /// By default, it does nothing
    ///
    ///
    /// @param subtreeRoot root of the subtree which the visitor leaves.
    default void subtreeLeft(T subtreeRoot) {
        // do nothing
    }
}
