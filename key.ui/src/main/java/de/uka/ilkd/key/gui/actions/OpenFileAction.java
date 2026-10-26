/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;
import java.nio.file.Path;
import javax.swing.*;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.KeYFileChooserLoadingOptions;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofSelectionDialog;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.jspecify.annotations.NullMarked;

@NullMarked
public class OpenFileAction extends MainWindowAction {
    public File lastSelectedPath;

    /**
     * The action-configuration setters are called on {@code this} while the receiver is still
     * under initialization (EISOP initialization check); safe here, suppressed with a scoped key.
     * The working directory lookup below must succeed: the action is only constructed from the
     * standalone GUI entry point after {@code PathConfig} setup, and the previous code crashed
     * with a NPE for a missing directory anyway (explicit crash-equivalent guard).
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public OpenFileAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Load...");
        setIcon(IconFactory.openKeYFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Browse and load problem or proof files.");
        Path workingDir = Main.getWorkingDir();
        if (workingDir == null) {
            throw new NullPointerException("No working directory configured.");
        }
        lastSelectedPath = workingDir.toFile();
    }

    public void actionPerformed(ActionEvent e) {
        KeYFileChooser fc = new KeYFileChooser(lastSelectedPath);
        fc.setDialogTitle("Select file to load proof or problem");
        fc.setSelectedFile(KeYFileChooser.getFileChooser("Select file to load proof or problem")
                .getSelectedFile());
        KeYFileChooserLoadingOptions options = fc.addLoadingOptions();
        fc.addBookmarkPanel();
        fc.prepare();
        fc.setFileFilter(KeYFileChooser.DEFAULT_FILTER);

        int result = fc.showOpenDialog(mainWindow);

        if (result == JFileChooser.APPROVE_OPTION) {
            File selectedFile = fc.getSelectedFile();
            if (selectedFile == null) {
                throw new NullPointerException("No file selected in the file chooser.");
            }
            Path file = selectedFile.toPath();
            lastSelectedPath = selectedFile;

            // special case proof bundles -> allow to select the proof to load
            if (ProofSelectionDialog.isProofBundle(file)) {
                Path proofPath = ProofSelectionDialog.chooseProofToLoad(file);
                if (proofPath == null) {
                    // canceled by user!
                } else {
                    mainWindow.loadProofFromBundle(file, proofPath);
                }
                return;
            }

            if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getNotifyLoadBehaviour()
                    && file.toString().endsWith(".java")) {
                JCheckBox checkbox = new JCheckBox("Don't show this warning again");
                Object[] message = { "When you load a Java file, all java files in the current",
                    "directory and all subdirectories will be loaded as well.", checkbox };
                JOptionPane.showMessageDialog(mainWindow, message, "Please note",
                    JOptionPane.WARNING_MESSAGE);
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                        .setNotifyLoadBehaviour(!checkbox.isSelected());
                ProofIndependentSettings.DEFAULT_INSTANCE.saveSettings();
            }

            var selectedProfile = options.getSelectedProfile();
            var additionalProfileOptions = options.getAdditionalProfileOptions();
            mainWindow.loadProblem(file, pl -> {
                pl.forceNewProfileOfNewProofs(selectedProfile != null);
                pl.setProfileOfNewProofs(selectedProfile);
                pl.setAdditionalProfileOptions(additionalProfileOptions);
                pl.setLoadSingleJavaFile(options.isOnlyLoadSingleJavaFile());
            });
        }
    }
}
