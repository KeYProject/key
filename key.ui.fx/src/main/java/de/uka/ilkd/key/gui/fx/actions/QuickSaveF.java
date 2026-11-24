/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.actions;

import java.io.File;
import java.nio.file.Path;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.util.KeYConstants;

import org.key_project.util.java.IOUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Quick save/quick load of the currently selected proof. Counter-part of the Swing actions
 * {@code de.uka.ilkd.key.gui.actions.QuickSaveAction} and
 * {@code de.uka.ilkd.key.gui.actions.QuickLoadAction} of the module {@code key.ui}: the proof is
 * immediately saved to a temporary location ({@value #QUICK_SAVE_PATH}, the OS's temp directory —
 * <b>not</b> the KeY config directory) and restored from there with the F5/F6 keys.
 * <p>
 * Swing semantics kept: a quick save without a selected proof warns ("No proof."); a failed save
 * warns with the error string; the quick load unconditionally loads the quick save location (a
 * missing file fails the load asynchronously). The quick save location never enters the recent
 * files list (Swing {@code RecentFileMenu.addNewToModelAndView}).
 */
public final class QuickSaveF {

    private static final Logger LOGGER = LoggerFactory.getLogger(QuickSaveF.class);

    /** The path to the quick save file (Swing {@code QuickSaveAction.QUICK_SAVE_PATH}). */
    public static final String QUICK_SAVE_PATH =
        IOUtil.getTempDirectory() + File.separator + ".quicksave.key";

    private QuickSaveF() {
    }

    /**
     * Immediately saves the currently selected proof to the temporary location
     * {@link #QUICK_SAVE_PATH} (Swing {@code QuickSaveAction.quickSave}).
     *
     * @param mainWindow the main window
     */
    public static void quickSave(MainWindowF mainWindow) {
        final Proof proof = mainWindow.getMediator().getSelectedProof();
        if (proof == null) {
            // unreachable: the action is disabled without a proof (Swing enableWhenProofLoaded)
            mainWindow.popupWarning("No proof.");
            return;
        }
        final String filename = QUICK_SAVE_PATH;

        String status = new ProofSaver(proof, Path.of(filename), KeYConstants.INTERNAL_VERSION)
                .save();

        if (status == null) {
            // success case
            status = "File quicksaved: " + filename;
        } else {
            mainWindow.popupWarning("Quicksaving file " + filename + " failed:\n" + status);
            LOGGER.info("Quicksaving file {} failed: {}", filename, status);
        }
        mainWindow.setStatusLine(status);
        LOGGER.info("Quicksave: {}", status);
    }

    /**
     * Load the file saved at the location described by {@link #quickSave} (Swing
     * {@code QuickLoadAction.quickLoad}: the quick save location is loaded like any other file,
     * unconditionally — a missing file fails the load).
     *
     * @param mainWindow the main window
     */
    public static void quickLoad(MainWindowF mainWindow) {
        mainWindow.openProofFile(Path.of(QUICK_SAVE_PATH));
    }
}
