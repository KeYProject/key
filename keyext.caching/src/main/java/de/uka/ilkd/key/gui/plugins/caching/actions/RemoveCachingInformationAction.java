/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.reference.ClosedBy;

import org.jspecify.annotations.NullMarked;

/**
 * Action to remove caching information on a goal closed by caching.
 *
 * @author Arne Keller
 */
@NullMarked
public final class RemoveCachingInformationAction extends KeyAction {

    /**
     * The KeY mediator.
     */
    private final KeYMediator mediator;
    /**
     * The node to apply the action on.
     */
    private final Node node;

    public RemoveCachingInformationAction(KeYMediator mediator, Node node) {
        this.mediator = mediator;
        this.node = node;

        setMenuPath("Proof Caching");
        setEnabled(node.lookup(ClosedBy.class) != null);

        setName("Re-open cached goal");
        putValue(SHORT_DESCRIPTION, "Make this an open goal again.");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        // remove associated info
        ClosedBy c = node.lookup(ClosedBy.class);
        if (c == null) {
            throw new NullPointerException("No caching reference to remove for node "
                + node.serialNr() + ".");
        }
        node.deregister(c, ClosedBy.class);
        // and re-open the goal
        Goal goal = node.proof().getClosedGoal(node);
        if (goal == null) {
            throw new NullPointerException("No closed goal to re-open for node "
                + node.serialNr() + ".");
        }
        node.proof().reOpenGoal(goal);
        // refresh selection to ensure UI is updated
        mediator.getSelectionModel().setSelectedNode(node);
    }
}
