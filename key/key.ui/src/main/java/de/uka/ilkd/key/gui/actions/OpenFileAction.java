// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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
        setName("Load");
        setIcon(IconFactory.openKeYFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Browse and load problem or proof files.");
        setAcceleratorLetter(KeyEvent.VK_O);
    }

    public void actionPerformed(ActionEvent e) {
        KeYFileChooser keYFileChooser = 
            KeYFileChooser.getFileChooser("Select file to load proof or problem");

        boolean loaded = keYFileChooser.showOpenDialog(mainWindow);

        if (loaded) {
            File file = keYFileChooser.getSelectedFile();

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

            if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getNotifyLoadBehaviour() &&
                    file.toString().endsWith(".java")) {
                JCheckBox checkbox = new JCheckBox("Don't show this warning again");
                Object[] message = { "When you load a Java file, all java files in the current",
                        "directory and all subdirectories will be loaded as well.",
                        checkbox };
                JOptionPane.showMessageDialog(mainWindow, message,
                        "Please note", JOptionPane.WARNING_MESSAGE);
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                            .setNotifyLoadBehaviour(!checkbox.isSelected());
                ProofIndependentSettings.DEFAULT_INSTANCE.saveSettings();
            }
            mainWindow.loadProblem(file);
        }

    }
}