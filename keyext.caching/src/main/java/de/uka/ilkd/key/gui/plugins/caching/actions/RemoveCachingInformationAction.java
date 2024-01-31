/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.reference.ClosedBy;

/**
 * Action to remove caching information on a goal closed by caching.
 *
 * @author Arne Keller
 */
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
        node.deregister(node.lookup(ClosedBy.class), ClosedBy.class);
        // and re-open the goal
        node.proof().reOpenGoal(node.proof().getClosedGoal(node));
        // refresh selection to ensure UI is updated
        mediator.getSelectionModel().setSelectedNode(node);
    }
}
