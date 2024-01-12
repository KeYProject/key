/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions.useractions;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * User action that modifies the proof in some way.
 * On undo: prunes proof to previous collection of open goals, selects previously active node.
 *
 * @author Arne Keller
 */
public abstract class ProofModifyingUserAction extends UserAction {
    /**
     * The open goals of the proof, before the user action is applied.
     * Will be restored (by pruning the proof) on undo.
     */
    private final Collection<Node> originalOpenGoals;
    /**
     * The node selected before the user action is performed.
     */
    private final Node originalSelection;

    /**
     * Save the current state of the proof.
     *
     * @param mediator the mediator
     * @param originalState the proof
     */
    protected ProofModifyingUserAction(KeYMediator mediator, Proof originalState) {
        super(mediator, originalState);
        this.originalOpenGoals =
            originalState.openGoals().stream().map(Goal::node).collect(Collectors.toList());
        this.originalSelection = mediator.getSelectedNode();
    }

    /**
     * Save the current state of the proof.
     * Mark the just modified node as an open goal.
     *
     * @param mediator the mediator
     * @param originalState the proof
     * @param justModifiedNode just modified node
     */
    protected ProofModifyingUserAction(KeYMediator mediator, Proof originalState,
            Node justModifiedNode) {
        super(mediator, originalState);
        List<Node> openGoals =
            originalState.openGoals().stream().map(Goal::node).collect(Collectors.toList());
        Node openGoalToReplace = null;
        for (Node openGoal : openGoals) {
            if (openGoal.parent() == justModifiedNode) {
                openGoalToReplace = openGoal;
                break;
            }
        }
        if (openGoalToReplace != null) {
            openGoals.remove(openGoalToReplace);
            openGoals.add(justModifiedNode);
        }
        this.originalOpenGoals = openGoals;
        this.originalSelection = mediator.getSelectedNode();
    }

    @Override
    public void undo() {
        for (Node n : originalOpenGoals) {
            n.proof().pruneProof(n);
        }
        mediator.getSelectionModel().setSelectedNode(originalSelection);
    }

    @Override
    public boolean canUndo() {
        return originalOpenGoals.stream().allMatch(proof::find) && proof.find(originalSelection);
    }
}
