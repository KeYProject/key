/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.actions;

import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.plugins.caching.CachingExtension;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;

/**
 * Action to search for suitable references on a single node.
 *
 * @author Arne Keller
 */
public final class CloseByReference extends KeyAction {
    /**
     * The caching extension.
     */
    private final CachingExtension cachingExtension;
    /**
     * The mediator.
     */
    private final KeYMediator mediator;
    /**
     * The node to try to close by reference.
     */
    private final Node node;

    /**
     * Construct new action.
     *
     * @param mediator the mediator
     * @param node the node
     */
    public CloseByReference(CachingExtension cachingExtension, KeYMediator mediator, Node node) {
        this.cachingExtension = cachingExtension;
        this.mediator = mediator;
        this.node = node;
        setName("Close by reference to other proof");
        setEnabled(!node.isClosed() && node.lookup(ClosedBy.class) == null);
        setMenuPath("Proof Caching");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        // nodes will be the open goals for which to
        // perform proof caching
        List<Node> nodes = new ArrayList<>();
        if (node.leaf()) {
            nodes.add(node);
        } else {
            node.subtreeIterator().forEachRemaining(n -> {
                if (n.leaf() && !n.isClosed()) {
                    nodes.add(n);
                }
            });
        }
        List<Integer> mismatches = new ArrayList<>();
        for (Node n : nodes) {
            // search other proofs for matching nodes
            ClosedBy c = ReferenceSearcher.findPreviousProof(
                mediator.getCurrentlyOpenedProofs(), n);
            if (c != null) {
                n.proof().closeGoal(n.proof().getOpenGoal(n));
                n.register(c, ClosedBy.class);
            } else {
                mismatches.add(n.serialNr());
            }
        }
        if (!nodes.isEmpty()) {
            cachingExtension.updateGUIState(nodes.get(0).proof());
        }
        if (!mismatches.isEmpty()) {
            // since e.getSource() is the popup menu, it is better to use the MainWindow
            // instance here as a parent
            JOptionPane.showMessageDialog(MainWindow.getInstance(),
                "No matching branch found for node(s) " + Arrays.toString(mismatches.toArray()),
                "Proof Caching error", JOptionPane.WARNING_MESSAGE);
        }
    }
}
