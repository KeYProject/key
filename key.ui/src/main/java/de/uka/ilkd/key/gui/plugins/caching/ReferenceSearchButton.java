/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;

/**
 * Status line button to indicate whether cached goals are present.
 *
 * @author Arne Keller
 */
public class ReferenceSearchButton extends JButton implements ActionListener, KeYSelectionListener {
    /**
     * Color used for the label if a reference is found.
     */
    private static final ColorSettings.ColorProperty COLOR_FINE =
        ColorSettings.define("caching.reference_found", "",
            new Color(80, 120, 0));

    /**
     * The mediator.
     */
    private final KeYMediator mediator;

    /**
     * Construct a new button.
     *
     * @param mediator the mediator
     */
    public ReferenceSearchButton(KeYMediator mediator) {
        super("Proof Caching");
        this.mediator = mediator;
        mediator.addKeYSelectionListener(this);
        addActionListener(this);
        setEnabled(false);
    }


    @Override
    public void actionPerformed(ActionEvent e) {
        Proof p = mediator.getSelectedProof();
        for (Goal goal : p.openEnabledGoals()) {
            ClosedBy c = ReferenceSearcher.findPreviousProof(mediator.getCurrentlyOpenedProofs(),
                goal.node());
            if (c != null) {
                p.closeGoal(goal);
                goal.node().register(c, ClosedBy.class);

                c.getProof()
                        .addProofDisposedListenerFirst(new CachingExtension.CopyBeforeDispose(
                            mediator, c.getProof(), p));
            }
        }
        var dialog =
            new ReferenceSearchDialog(p, new DefaultReferenceSearchDialogListener(mediator));
        dialog.setVisible(true);
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
        Proof p = e.getSource().getSelectedProof();
        updateState(p);
    }

    /**
     * Update the UI state of this button.
     *
     * @param p the currently selected proof
     */
    public void updateState(Proof p) {
        if (p == null) {
            setText("Proof Caching");
            setForeground(null);
            setEnabled(false);
            return;
        }
        long foundRefs =
            p.closedGoals().stream().filter(g -> g.node().lookup(ClosedBy.class) != null).count();
        if (foundRefs > 0) {
            setText(String.format("Proof Caching (%d)", foundRefs));
            setForeground(COLOR_FINE.get());
            setEnabled(true);
        } else {
            setText("Proof Caching");
            setForeground(null);
            setEnabled(false);
        }
    }
}
