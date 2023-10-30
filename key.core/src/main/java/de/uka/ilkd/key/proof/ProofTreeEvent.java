/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Encapsulates information describing changes to a proof tree, and used to notify proof tree
 * listeners of the change.
 */

public class ProofTreeEvent {

    private final Proof source;
    private Node node;
    private Goal goal;
    private ImmutableList<Goal> goals = ImmutableSLList.nil();

    /**
     * Create ProofTreeEvent for an event that happens at the specified node.
     */
    public ProofTreeEvent(Proof source, Node node) {
        this.source = source;
        this.node = node;
    }

    /**
     * Create ProofTreeEvent for an event that happens at no particular node.
     */
    public ProofTreeEvent(Proof source) {
        this.source = source;
    }

    /**
     * Create ProofTreeEvent for the event that happened to the given goal
     */
    public ProofTreeEvent(Proof source, Goal goal) {
        this.source = source;
        this.goal = goal;
    }

    /**
     * Create ProofTreeEvent for the event that affects the goals given in the list.
     */
    public ProofTreeEvent(Proof source, ImmutableList<Goal> goals) {
        this.source = source;
        this.goals = goals;
    }

    public Node getNode() {
        return node;
    }

    public Proof getSource() {
        return source;
    }

    public Goal getGoal() {
        return goal;
    }

    public ImmutableList<Goal> getGoals() {
        return goals;
    }

    public String toString() {
        return "ProofTreeEvent: " + ((node != null) ? "node " : "")
            + ((goal != null) ? "goal " : "") + ((!goals.isEmpty()) ? "goals " : "");
    }
}
