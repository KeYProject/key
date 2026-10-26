/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.jspecify.annotations.NullMarked;

/**
 * Saves the currently selected proof as a zip archive with file extension "zproof". The bundle
 * contains all files needed to successfully reload the proof.
 *
 * @author Wolfram Pfeifer
 */
@NullMarked
public final class SaveBundleAction extends MainWindowAction {

    private static final long serialVersionUID = 5275664295885839738L;

    /**
     * Creates a new SaveBundleAction with the required listeners.
     *
     * @param mainWindow the main window of the program
     */
    public SaveBundleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Save Proof as Bundle...");
        setIcon(IconFactory.saveBundle(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Save current proof as a bundle containing all files to successfully reload "
            + "the proof (disabled when option \"Allow proof bundle saving\" is set).");

        // react to setting changes
        GeneralSettings settings = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        settings.addPropertyChangeListener(e -> updateStatus());

        // react to changes of proof selection
        mainWindow.getMediator().addKeYSelectionListener(new KeYSelectionListener() {

            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                updateStatus();
            }
        });

        updateStatus();
    }

    private void updateStatus() {
        // enable only if there is a proof
        setEnabled(mainWindow.getMediator().getSelectedProof() != null);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (mainWindow.getMediator().ensureProofLoaded()) {
            // Try to save back to file where proof was initially loaded from
            final Proof selectedProof = mainWindow.getMediator().getSelectedProof();
            if (selectedProof == null) {
                // A proof is ensured to be loaded above; a {@code null} here is a concurrent
                // state change, crash-equivalent to the previous NPE in the saver.
                throw new NullPointerException("No proof loaded to save.");
            }
            mainWindow.getUserInterface().saveProofBundle(selectedProof);
        } else {
            mainWindow.popupWarning("No proof.", "Oops...");
        }
    }
}
