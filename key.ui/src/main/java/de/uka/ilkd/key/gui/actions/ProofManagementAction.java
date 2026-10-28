/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofManagementDialog;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;

import org.jspecify.annotations.NullMarked;

/**
 * Shows the proof management dialog
 */
@NullMarked
public final class ProofManagementAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 7696620742992568551L;

    /**
     * The action-configuration calls and the mediator queries below operate on {@code this} while
     * the receiver is still under initialization (EISOP initialization check); safe here since the
     * attached listener only reacts to later selection events, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public ProofManagementAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Proof Management");
        setTooltip("Browse contracts and possible proof targets");
        setIcon(IconFactory.proofMgt(16));

        setEnabled(enabled());

        getMediator().addKeYSelectionListener(new KeYSelectionListener() {
            /** focused node has changed */
            public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
            }

            /**
             * the selected proof has changed. Enable or disable action depending on whether a proof
             * is
             * available or not
             */
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                setEnabled(enabled());
            }
        });
    }

    private boolean enabled() {
        Proof proof = getMediator().getSelectedProof();
        if (proof == null) {
            return false;
        }
        JavaModel javaModel = proof.getServices().getJavaModel();
        return javaModel != null && !javaModel.isEmpty();
    }

    public void actionPerformed(ActionEvent e) {
        showProofManagement();
    }

    private void showProofManagement() {
        Proof proof = getMediator().getSelectedProof();
        if (proof == null) {
            mainWindow.notify(new GeneralFailureEvent("Please load a proof first"));
        } else {
            ProofEnvironment env = proof.getEnv();
            if (env == null) {
                // a loaded proof always has an environment; the original code dereferenced it
                throw new NullPointerException("No proof environment available.");
            }
            ProofManagementDialog.showInstance(env.getInitConfigForEnvironment());
        }
    }
}
