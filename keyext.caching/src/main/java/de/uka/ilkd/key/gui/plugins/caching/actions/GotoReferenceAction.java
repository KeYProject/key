/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.reference.ClosedBy;

import org.jspecify.annotations.NullMarked;

/**
 * Action to go the referenced proof.
 *
 * @author Arne Keller
 */
@NullMarked
public final class GotoReferenceAction extends KeyAction {

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
        ClosedBy c = node.lookup(ClosedBy.class);
        if (c == null) {
            throw new NullPointerException("No reference found for node " + node.serialNr() + ".");
        }
        Node ref = c.node();
        mediator.getSelectionModel().setSelectedNode(ref);
    }
}
