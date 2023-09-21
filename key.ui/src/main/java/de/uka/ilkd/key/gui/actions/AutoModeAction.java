/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import javax.swing.Action;
import javax.swing.Icon;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.useractions.AutoModeUserAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;

import org.key_project.util.collection.ImmutableList;

public final class AutoModeAction extends MainWindowAction {

    private static final KeyStroke START_KEY =
        KeyStroke.getKeyStroke(KeyEvent.VK_SPACE, InputEvent.CTRL_DOWN_MASK);
    private static final KeyStroke STOP_KEY = KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0);
    /**
     *
     */
    private static final long serialVersionUID = -7702898691162947994L;
    final Icon startLogo = IconFactory.autoModeStartLogo(MainWindow.TOOLBAR_ICON_SIZE);
    final Icon stopLogo = IconFactory.autoModeStopLogo(MainWindow.TOOLBAR_ICON_SIZE);

    private Proof associatedProof;

    private final ProofTreeListener ptl = new ProofTreeAdapter() {

        public void proofStructureChanged(ProofTreeEvent e) {
            if (e.getSource() == associatedProof) {
                enable();
            }
        }

        public void proofClosed(ProofTreeEvent e) {
            if (e.getSource() == associatedProof) {
                enable();
            }
        }

        public void proofGoalsAdded(ProofTreeEvent e) {
            Proof p = e.getSource();
            ImmutableList<Goal> newGoals = e.getGoals();
            // Check for a closed goal ...
            if ((newGoals.size() == 0) && (!p.closed())) {
                // No new goals have been generated ...
                mainWindow.setStatusLine("1 goal closed, " + p.openGoals().size() + " remaining");
            }
        }
    };

    public AutoModeAction(MainWindow mainWindow) {
        super(mainWindow);
        associatedProof = getMediator().getSelectedProof();
        putValue("hideActionText", Boolean.TRUE);
        setName(getStartCommand());
        setTooltip(MainWindow.AUTO_MODE_TEXT);
        setIcon(startLogo);

        enable();

        if (associatedProof != null && !associatedProof.containsProofTreeListener(ptl)) {
            associatedProof.addProofTreeListener(ptl);
        }

        getMediator().addKeYSelectionListener(new KeYSelectionListener() {
            /** focused node has changed */
            public void selectedNodeChanged(KeYSelectionEvent e) {
            }

            /**
             * the selected proof has changed. Enable or disable action depending whether a proof is
             * available or not
             */
            public void selectedProofChanged(KeYSelectionEvent e) {
                if (associatedProof != null) {
                    associatedProof.removeProofTreeListener(ptl);
                }

                associatedProof = e.getSource().getSelectedProof();
                enable();

                if (associatedProof != null) {
                    associatedProof.addProofTreeListener(ptl);
                }
            }
        });

        // This method delegates the request only to the UserInterfaceControl which implements the
        // functionality.
        // No functionality is allowed in this method body!
        getMediator().getUI().getProofControl().addAutoModeListener(new AutoModeListener() {

            /**
             * invoked if automatic execution has started
             */
            public void autoModeStarted(ProofEvent e) {
                if (associatedProof != null) {
                    associatedProof.removeProofTreeListener(ptl);
                }
                putValue(Action.NAME, "Stop");
                putValue(Action.SMALL_ICON, stopLogo);
                putValue(Action.ACCELERATOR_KEY, STOP_KEY);
            }

            /**
             * invoked if automatic execution has stopped
             */
            public void autoModeStopped(ProofEvent e) {
                if (associatedProof != null && associatedProof == e.getSource()
                        && !associatedProof.containsProofTreeListener(ptl)) {
                    associatedProof.addProofTreeListener(ptl);
                }
                putValue(Action.NAME, getStartCommand());
                putValue(Action.SMALL_ICON, startLogo);
                putValue(Action.ACCELERATOR_KEY, START_KEY);
            }

        });

    }

    public void enable() {
        setEnabled(associatedProof != null && !associatedProof.closed());
    }

    private String getStartCommand() {
        if (associatedProof != null && !associatedProof.root().leaf()) {
            return "Continue";
        } else {
            return "Start";
        }
    }

    public void actionPerformed(ActionEvent e) {
        // Unfortunately, when clicking the button twice
        // (very fast), the glasspane won't be quick
        // enough to catch the second event. Therefore
        // we make a second check (which is a %%%HACK)
        if (!getMediator().isInAutoMode()) {
            KeYMediator r = getMediator();
            Proof proof = r.getSelectedProof();
            if (r.getUI().getProofControl().isAutoModeSupported(proof)) {
                // This method delegates the request only to the UserInterfaceControl which
                // implements the functionality.
                // No functionality is allowed in this method body!
                new AutoModeUserAction(r, proof).actionPerformed(e);
            }
        } else {
            // this interface is no longer used (MU)
            // getMediator().interrupted(e);
            // This method delegates the request only to the UserInterfaceControl which implements
            // the functionality.
            // No functionality is allowed in this method body!
            getMediator().getUI().getProofControl().stopAutoMode();
        }
    }

}
