/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.actions;

import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.plugins.caching.CachingExtension;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;

/**
 * Proof context menu action to perform proof caching for all open goals on that proof.
 *
 * @author Arne Keller
 */
public class CloseAllByReference extends KeyAction {
    /**
     * The caching extension.
     */
    private final CachingExtension cachingExtension;
    /**
     * The KeY mediator.
     */
    private final KeYMediator mediator;
    /**
     * The proof whose open goals we try to close by reference.
     */
    private final Proof proof;

    /**
     * Construct new action.
     *
     * @param cachingExtension the caching extension
     * @param mediator the KeY mediator
     * @param proof the proof to work on
     */
    public CloseAllByReference(CachingExtension cachingExtension, KeYMediator mediator,
            Proof proof) {
        this.cachingExtension = cachingExtension;
        this.mediator = mediator;
        this.proof = proof;
        setName("Run proof caching search on open goals");
        setEnabled(!proof.closed());
        setMenuPath("Proof Caching");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        // nodes will be the open goals for which to
        // perform proof caching
        List<Node> nodes = new ArrayList<>();
        proof.openGoals().forEach(x -> nodes.add(x.node()));
        int matches = 0;
        for (Node n : nodes) {
            // search other proofs for matching nodes
            ClosedBy c = ReferenceSearcher.findPreviousProof(
                mediator.getCurrentlyOpenedProofs(), n);
            if (c != null) {
                n.proof().closeGoal(n.proof().getOpenGoal(n));
                n.register(c, ClosedBy.class);
                matches++;
            }
        }
        if (matches > 0) {
            cachingExtension.updateGUIState();
            // since e.getSource() is the popup menu, it is better to use the MainWindow
            // instance here as a parent
            JOptionPane.showMessageDialog(MainWindow.getInstance(),
                "Successfully closed " + matches + " open goal(s) by cache",
                "Proof Caching", JOptionPane.INFORMATION_MESSAGE);
        } else {
            JOptionPane.showMessageDialog(MainWindow.getInstance(),
                "Failed to find any matches",
                "Proof Caching", JOptionPane.ERROR_MESSAGE);
        }
    }
}
