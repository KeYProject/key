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

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;

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
            // Try to save back to file where proof was initially loaded from
            final Proof selectedProof = mainWindow.getMediator().getSelectedProof();
            mainWindow.getUserInterface().noAutoSave();
            mainWindow.getUserInterface().saveProof(selectedProof, ".proof");
            mainWindow.getUserInterface().resetAutoSave();
        } else {
            mainWindow.popupWarning("No proof.", "Oops...");
        }
    }
}