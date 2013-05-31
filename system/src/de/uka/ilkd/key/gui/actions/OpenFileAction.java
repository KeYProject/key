// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.io.File;

import javax.swing.JCheckBox;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.util.GuiUtilities;

import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;

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
        KeYFileChooser keYFileChooser = 
            GuiUtilities.getFileChooser("Select file to load proof or problem");
        
        boolean loaded = keYFileChooser.showOpenDialog(mainWindow);
        
        if (loaded) {
            File file = keYFileChooser.getSelectedFile();
            if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getNotifyLoadBehaviour() && file.toString().endsWith(".java")) {
                JCheckBox checkbox = new JCheckBox("Don't show this warning again");
                Object[] message = { "When you load a Java file, all java files in the current",
                        "directory and all subdirectories will be loaded as well.",
                        checkbox };
                JOptionPane.showMessageDialog(mainWindow, message, 
                        "Please note", JOptionPane.WARNING_MESSAGE);
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setNotifyLoadBehaviour(!checkbox.isSelected());
                ProofIndependentSettings.DEFAULT_INSTANCE.saveSettings();
            }
            mainWindow.loadProblem(file);
        }
        
    }
}