/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public final class AbandonTaskAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 915588190956945751L;

    private final @Nullable Proof proof;

    /**
     * The action-configuration calls and the {@code enableWhenProofLoaded(this)} registration
     * operate on {@code this} while the receiver is still under initialization (EISOP
     * initialization check); safe here since the listener only reacts to later selection events,
     * suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:method.invocation.invalid",
        "nullness:argument.type.incompatible" })
    public AbandonTaskAction(MainWindow mainWindow, @Nullable Proof proof) {
        super(mainWindow);
        setName("Abandon Proof");
        setIcon(IconFactory.abandon(16));
        setTooltip("Drop current proof.");

        getMediator().enableWhenProofLoaded(this);

        this.proof = proof;
    }

    public synchronized void actionPerformed(ActionEvent e) {
        boolean removalConfirmed = getMediator().getUI().confirmTaskRemoval("Are you sure?");
        if (removalConfirmed) {
            // abandon proof that is currently in auto mode: first stop auto mode
            if (getMediator().isInAutoMode()) {
                getMediator().getUI().getProofControl().stopAutoMode();
            }
            if (proof == null) {
                Proof selectedProof = getMediator().getSelectedProof();
                if (selectedProof == null) {
                    throw new NullPointerException("No proof selected to abandon.");
                }
                selectedProof.dispose();
            } else {
                proof.dispose();
            }
        }
    }

}
