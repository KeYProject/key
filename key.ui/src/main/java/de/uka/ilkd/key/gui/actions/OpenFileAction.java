package de.uka.ilkd.key.gui.actions;

import java.awt.event.*;
import java.io.File;
import java.nio.file.Path;

import javax.swing.*;

import de.uka.ilkd.key.gui.ProofSelectionDialog;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

public class OpenFileAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = -8548805965130100236L;

    public OpenFileAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Load...");
        setIcon(IconFactory.openKeYFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Browse and load problem or proof files.");
        setAcceleratorLetter(KeyEvent.VK_O);
    }

    public void actionPerformed(ActionEvent e) {
        KeYFileChooser fc = KeYFileChooser.getFileChooser("Select file to load proof or problem");
        fc.setFileFilter(KeYFileChooser.DEFAULT_FILTER);

        int result = fc.showOpenDialog(mainWindow);

        if (result == JFileChooser.APPROVE_OPTION) {
            File file = fc.getSelectedFile();

            // special case proof bundles -> allow to select the proof to load
            if (ProofSelectionDialog.isProofBundle(file.toPath())) {
                Path proofPath = ProofSelectionDialog.chooseProofToLoad(file.toPath());
                if (proofPath == null) {
                    // canceled by user!
                    return;
                } else {
                    mainWindow.loadProofFromBundle(file, proofPath.toFile());
                    return;
                }
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
            mainWindow.loadProblem(file);
        }
    }
}
