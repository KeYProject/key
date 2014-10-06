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

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.io.File;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

/**
 * Saves the current selected proof.
 */
public final class SaveFileAction extends MainWindowAction {
    
    /**
     * 
     */
    private static final long serialVersionUID = -5479654127272775831L;

    public SaveFileAction(MainWindow mainWindow) {
	super(mainWindow);
        setName("Save");
        setIcon(IconFactory.saveFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Save current proof.");
        setAcceleratorLetter(KeyEvent.VK_S);
        
        mainWindow.getMediator().enableWhenProofLoaded(this);
    }

    public void actionPerformed(ActionEvent e) {
        if (mainWindow.getMediator().ensureProofLoaded()) {
            final KeYFileChooser jFC = GuiUtilities.getFileChooser("Choose filename to save proof");
            // Try to save back to file where proof was initially loaded from
            File selectedFile = null;
            final Proof selectedProof = mainWindow.getMediator().getSelectedProof();
            if (selectedProof != null) {
               selectedFile = selectedProof.getProofFile();
            }
            // Suggest default file name if required
            final String defaultName = MiscTools.toValidFileName(selectedProof.name().toString()) + ".proof";
            if (selectedFile == null) {
               selectedFile = new File(jFC.getCurrentDirectory(), defaultName);
            }
            final Pair<Boolean, Pair<File, Boolean>> res =
                    jFC.showSaveDialog(mainWindow, defaultName + ".proof", false);
            boolean saved = res.first;
            boolean newDir = res.second.second;
            if (saved) {
                mainWindow.saveProof(jFC.getSelectedFile());
            } else if (newDir) {
                File dir = res.second.first;
                if (!dir.delete()) {
                    dir.deleteOnExit();
                }
            }
            jFC.resetPath();
        } else {
            mainWindow.popupWarning("No proof.", "Oops...");
        }
    }
}