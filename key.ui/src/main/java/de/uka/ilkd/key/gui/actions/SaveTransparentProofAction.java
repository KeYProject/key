/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.Component;
import java.awt.event.ActionEvent;
import java.io.File;
import java.nio.file.Path;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.SwingWorker;

import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.lemma.TransparentProofSaver;
import de.uka.ilkd.key.util.MiscTools;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Saves the selected proof in its transparent form: eligible one step simplifier applications
 * are elaborated into generated, separately provable lemma taclets (introduction plus taclet
 * application) before saving. The proof itself is left unchanged.
 *
 * @see TransparentProofSaver
 */
public final class SaveTransparentProofAction extends MainWindowAction {

    private static final long serialVersionUID = 1L;
    private static final Logger LOGGER =
        LoggerFactory.getLogger(SaveTransparentProofAction.class);

    /**
     * The proof to save; if {@code null}, the currently selected proof is saved (used for the
     * task list context menu, which acts on the proof under the mouse pointer).
     */
    private final Proof proof;

    public SaveTransparentProofAction(MainWindow mainWindow) {
        this(mainWindow, null);
    }

    public SaveTransparentProofAction(MainWindow mainWindow, Proof proof) {
        super(mainWindow);
        this.proof = proof;
        setName("Save Transparent Proof...");
        setTooltip("Save the proof with One Step Simplification steps elaborated into "
            + "generated, separately provable lemma taclets.");
        if (proof == null) {
            mainWindow.getMediator().enableWhenProofLoaded(this);
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        final Proof toSave =
            proof != null ? proof : mainWindow.getMediator().getSelectedProof();
        if (toSave == null) {
            mainWindow.popupWarning("No proof.", "Oops...");
            return;
        }
        saveTransparent(mainWindow, toSave, mainWindow);
    }

    /**
     * Asks for a file name and saves the given proof in its transparent form (in the
     * background, since elaboration replays the whole proof).
     */
    public static void saveTransparent(MainWindow mainWindow, Proof proof, Component parent) {
        final KeYFileChooser fileChooser =
            KeYFileChooser.getFileChooser("Choose filename to save transparent proof");
        fileChooser.setSelectedFile(new File(
            MiscTools.toValidFileName(proof.name().toString()) + ".transparent.proof"));
        if (fileChooser.showSaveDialog(parent) != JFileChooser.APPROVE_OPTION) {
            return;
        }
        final Path file = fileChooser.getSelectedFile().toPath();

        mainWindow.setStatusLine("Elaborating proof into its transparent form ...");
        new SwingWorker<TransparentProofSaver.Result, Void>() {
            @Override
            protected TransparentProofSaver.Result doInBackground() throws Exception {
                return TransparentProofSaver.save(proof, file);
            }

            @Override
            protected void done() {
                try {
                    final TransparentProofSaver.Result result = get();
                    mainWindow.setStatusLine("Transparent proof saved to " + file + " ("
                        + result.elaborated() + " simplifier application(s) elaborated into "
                        + result.lemmas() + " lemma(s), " + result.copiedOss()
                        + " copied unchanged)");
                } catch (Exception exception) {
                    LOGGER.error("Saving transparent proof failed", exception);
                    mainWindow.setStatusLine("Saving transparent proof failed");
                    JOptionPane.showMessageDialog(parent,
                        "Saving the transparent proof failed:\n" + exception.getMessage(),
                        "Save Transparent Proof", JOptionPane.ERROR_MESSAGE);
                }
            }
        }.execute();
    }
}
