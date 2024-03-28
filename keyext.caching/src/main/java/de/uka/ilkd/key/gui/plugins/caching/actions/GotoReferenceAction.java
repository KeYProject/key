/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.actions;

import java.awt.event.ActionEvent;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.reference.ClosedBy;

/**
 * Action to go the referenced proof.
 *
 * @author Arne Keller
 */
public final class GotoReferenceAction extends KeyAction {

    /**
     * The KeY mediator.
     */
    private final KeYMediator mediator;
    /**
     * The node which references another proof.
     */
    private final Node node;

    /**
     * Construct a new action.
     *
     * @param mediator KeY mediator
     * @param node the node to jump from
     */
    public GotoReferenceAction(KeYMediator mediator, Node node) {
        this.mediator = mediator;
        this.node = node;

        setMenuPath("Proof Caching");
        var closedBy = node.lookup(ClosedBy.class);
        setEnabled(closedBy != null);

        setName("Go to referenced proof");
        putValue(SHORT_DESCRIPTION, "Select the equivalent node in the other proof.");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Node ref = node.lookup(ClosedBy.class).node();
        if (mediator.getCurrentlyOpenedProofs().contains(ref.proof())) {
            mediator.getSelectionModel().setSelectedNode(ref);
        } else {
            JOptionPane.showMessageDialog(MainWindow.getInstance(),
                "Cannot go to referenced proof:" +
                    "\nit is an auxiliary proof loaded from the caching database",
                "Proof Caching", JOptionPane.ERROR_MESSAGE);
        }
    }
}
