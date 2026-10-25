/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.actions;

import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.plugins.caching.CachingExtension;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;

import org.jspecify.annotations.NullMarked;

/**
 * Proof context menu action to perform proof caching for all open goals on that proof.
 *
 * @author Arne Keller
 */
@NullMarked
public class CloseAllByReference extends KeyAction {
    /**
     * The caching extension.
     */
    private final CachingExtension cachingExtension;
    /**
     * The mediator.
     */
    private final KeYMediator mediator;
    /**
     * The proof whose open goals we try to close by reference.
     */
    private final Proof proof;

    /**
     * Construct new action.
     *
     * @param mediator the mediator
     * @param proof the proof
     *        <p>
     *        The setters below are called on {@code this} while the receiver is still under
     *        initialization (EISOP initialization check); safe here since all fields are set
     *        before the calls, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public CloseAllByReference(CachingExtension cachingExtension, KeYMediator mediator,
            Proof proof) {
        this.cachingExtension = cachingExtension;
        this.mediator = mediator;
        this.proof = proof;
        setName("Run proof caching search for open goals");
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
                Goal goal = n.proof().getOpenGoal(n);
                if (goal == null) {
                    throw new NullPointerException("No open goal for node " + n.serialNr() + ".");
                }
                n.proof().closeGoal(goal);
                n.register(c, ClosedBy.class);
                matches++;
            }
        }
        if (matches > 0) {
            cachingExtension.updateGUIState(proof);
            // since e.getSource() is the popup menu, it is better to use the MainWindow
            // instance here as a parent
            JOptionPane.showMessageDialog(MainWindow.getInstance(),
                "Successfully closed " + matches + " open goal(s) by cache",
                "Proof Caching info", JOptionPane.INFORMATION_MESSAGE);
        }
    }
}
