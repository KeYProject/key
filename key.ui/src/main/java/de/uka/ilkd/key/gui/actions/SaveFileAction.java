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

/**
 * Saves the current selected proof.
 */
@NullMarked
public final class SaveFileAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = -5479654127272775831L;

    /**
     * The action-configuration calls and the {@code enableWhenProofLoaded(this)} registration
     * operate on {@code this} while the receiver is still under initialization (EISOP
     * initialization check); safe here since the listener only reacts to later selection events,
     * suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:method.invocation.invalid",
        "nullness:argument.type.incompatible" })
    public SaveFileAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Save...");
        setIcon(IconFactory.saveFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Save current proof.");
        mainWindow.getMediator().enableWhenProofLoaded(this);
    }

    public void actionPerformed(ActionEvent e) {
        if (mainWindow.getMediator().ensureProofLoaded()) {
            // Try to save back to file where proof was initially loaded from
            final Proof selectedProof = mainWindow.getMediator().getSelectedProof();
            if (selectedProof == null) {
                // A proof is ensured to be loaded above; a {@code null} here is a concurrent
                // state change, crash-equivalent to the previous NPE in the saver.
                throw new NullPointerException("No proof loaded to save.");
            }
            mainWindow.getUserInterface().saveProof(selectedProof, ".proof");
        } else {
            mainWindow.popupWarning("No proof.", "Oops...");
        }
    }
}
