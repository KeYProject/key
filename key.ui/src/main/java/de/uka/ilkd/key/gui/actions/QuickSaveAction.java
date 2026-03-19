/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.util.KeYConstants;

import org.key_project.util.java.IOUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Immediately saves the currently selected proof to a temporaly location. This feature can be
 * conveniently accessed with the F5 key.
 *
 * @author bruns
 */
public final class QuickSaveAction extends MainWindowAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(QuickSaveAction.class);
    private static final long serialVersionUID = -7084304175671744403L;

    /** The OS's tmp directory. */
    private static final File TMP_DIR = IOUtil.getTempDirectory();

    /** The path to the quick save file. */
    public static final String QUICK_SAVE_PATH = TMP_DIR + File.separator + ".quicksave.key";

    /**
     * Create a new action.
     *
     * @param mainWindow the main window.
     */
    public QuickSaveAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Quicksave");
        setTooltip("Save current proof to a temporal location.");
        mainWindow.getMediator().enableWhenProofLoaded(this);
    }

    /**
     * Immediately saves the currently selected proof to a temporaly location.
     *
     * @param mainWindow the main window.
     */
    public static void quickSave(MainWindow mainWindow) {
        if (mainWindow.getMediator().ensureProofLoaded()) {
            final String filename = QUICK_SAVE_PATH;
            final Proof proof = mainWindow.getMediator().getSelectedProof();

            String status = new ProofSaver(proof, filename, KeYConstants.INTERNAL_VERSION).save();

            if (status == null) {
                // success case
                status = "File quicksaved: " + filename;
            } else {
                mainWindow.popupWarning(
                    "Quicksaving file " + filename + " failed:\n" + status,
                    "Quicksave failed");
                LOGGER.debug("Quicksaving file {} failed.", filename, status);
            }
            mainWindow.setStatusLine(status);
            LOGGER.debug(status);
        } else {
            mainWindow.popupWarning("No proof.", "Oops...");
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        quickSave(mainWindow);
    }
}
