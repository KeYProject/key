/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions.useractions;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * User action to start auto mode on a specific goal.
 *
 * @author Arne Keller
 */
public class RunStrategyOnNodeUserAction extends ProofModifyingUserAction {

    /**
     * The node the action was invoked on (i.e. the selected proof node).
     */
    private final Node invokedNode;

    /**
     * Construct a new user action.
     *
     * @param mediator the mediator
     * @param proof the proof
     * @param invokedNode the node to start auto mode on
     */
    public RunStrategyOnNodeUserAction(KeYMediator mediator, Proof proof, Node invokedNode) {
        super(mediator, proof);
        this.invokedNode = invokedNode;
    }

    @Override
    public String name() {
        return "Strategy: Auto Mode";
    }

    @Override
    protected void apply() {
        Goal invokedGoal = proof.getOpenGoal(invokedNode);
        KeYMediator r = mediator;
        // is the node a goal?
        if (invokedGoal == null) {
            ImmutableList<Goal> enabledGoals =
                proof.getSubtreeEnabledGoals(invokedNode);
            // This method delegates the request only to the UserInterfaceControl
            // which implements the functionality.
            // No functionality is allowed in this method body!
            mediator.getUI().getProofControl().startAutoMode(r.getSelectedProof(),
                enabledGoals);
        } else {
            // This method delegates the request only to the UserInterfaceControl
            // which implements the functionality.
            // No functionality is allowed in this method body!
            mediator.getUI().getProofControl().startAutoMode(r.getSelectedProof(),
                ImmutableSLList.<Goal>nil().prepend(invokedGoal));
        }
    }
}
