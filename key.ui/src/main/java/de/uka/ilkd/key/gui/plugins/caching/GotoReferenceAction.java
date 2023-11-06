/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.reference.ClosedBy;

/**
 * Action to go the referenced proof.
 *
 * @author Arne Keller
 */
public class GotoReferenceAction extends KeyAction {

    private final KeYMediator mediator;
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
        setEnabled(node.lookup(ClosedBy.class) != null);

        setName("Go to referenced proof");
        putValue(SHORT_DESCRIPTION, "Select the equivalent node in the other proof.");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Node ref = node.lookup(ClosedBy.class).getNode();
        mediator.getSelectionModel().setSelectedNode(ref);
    }
}
