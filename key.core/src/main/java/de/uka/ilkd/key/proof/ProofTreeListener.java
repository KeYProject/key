/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

public interface ProofTreeListener {

    /**
     * The node mentioned in the ProofTreeEvent has changed, and/or there are new descendants of
     * that node. Any nodes that are not descendants of that node are unaffected.
     */
    default void proofExpanded(ProofTreeEvent e) {

    }

    /**
     * The proof tree under the node mentioned in the ProofTreeEvent is in pruning phase. The
     * subtree of node will be removed after this call but at this point the subtree can still be
     * traversed (e.g. in order to free the nodes in caches). The method proofPruned is called, when
     * the nodes are disconnect from node.
     *
     * @param e proof tree event specifying the node to be pruned
     */
    default void proofIsBeingPruned(ProofTreeEvent e) {

    }

    /**
     * The proof tree has been pruned under the node mentioned in the ProofTreeEvent. In other
     * words, that node should no longer have any children now. Any nodes that were not descendants
     * of that node are unaffected.
     *
     * @param e proof tree event specifying the pruned node
     */
    default void proofPruned(ProofTreeEvent e) {

    }

    /**
     * The structure of the proof has changed radically. Any client should rescan the whole proof
     * tree.
     */
    default void proofStructureChanged(ProofTreeEvent e) {

    }

    /**
     * The proof trees has been closed (the list of goals is empty).
     */
    default void proofClosed(ProofTreeEvent e) {

    }

    /**
     * The goal mentioned in the ProofEvent has been removed from the list of goals.
     */
    default void proofGoalRemoved(ProofTreeEvent e) {

    }

    /**
     * The goals mentiones in the list of added goals in the proof event have been added to the
     * proof
     */
    default void proofGoalsAdded(ProofTreeEvent e) {

    }

    /**
     * The goals mentiones in the list of added goals in the proof event have been added to the
     * proof
     */
    default void proofGoalsChanged(ProofTreeEvent e) {

    }

    /**
     * If the notes of a {@link NodeInfo} of a proof tree {@link Node} have changed.
     *
     * @param e The {@link ProofTreeEvent}.
     */
    default void notesChanged(ProofTreeEvent e) {

    }
}
