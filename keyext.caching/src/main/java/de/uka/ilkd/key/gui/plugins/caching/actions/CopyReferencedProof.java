/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.actions;

import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Action to copy referenced proof steps to the new proof.
 *
 * @author Arne Keller
 */
public final class CopyReferencedProof extends KeyAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(CopyReferencedProof.class);

    /**
     * The mediator.
     */
    private final KeYMediator mediator;
    /**
     * The nodes to copy the steps to.
     */
    private final List<Node> nodes;

    /**
     * Construct a new action.
     *
     * @param mediator the mediator
     * @param node the node to apply the action on
     */
    public CopyReferencedProof(KeYMediator mediator, Node node) {
        this.mediator = mediator;
        this.nodes = new ArrayList<>();
        setName("Copy referenced proof steps here");
        var iter = node.leavesIterator();
        while (iter.hasNext()) {
            var goal = iter.next();
            if (goal.isClosed() && goal.lookup(ClosedBy.class) != null) {
                nodes.add(goal);
            }
        }
        setEnabled(!nodes.isEmpty());
        setMenuPath("Proof Caching");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        for (Node node : nodes) {
            ClosedBy c = node.lookup(ClosedBy.class);
            Goal current = node.proof().getClosedGoal(node);
            try {
                mediator.stopInterface(true);
                new CopyingProofReplayer(c.proof(), node.proof()).copy(c.node(), current,
                    c.nodesToSkip());
                mediator.startInterface(true);
            } catch (Exception ex) {
                LOGGER.error("failed to copy proof ", ex);
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), ex);
            }
        }
    }
}
