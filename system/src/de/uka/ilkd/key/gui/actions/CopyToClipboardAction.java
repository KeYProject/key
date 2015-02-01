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

import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.pp.PosInSequent;

import de.uka.ilkd.key.gui.nodeviews.CurrentGoalView;

/**
 * Copy a term that is currently selected (i.e., under the mouse cursor)
 * in the current goal view to the default system clip board.
 * @author bruns
 */
public class CopyToClipboardAction extends MainWindowAction {
    
    private static final long serialVersionUID = -6193181877353785015L;

    public CopyToClipboardAction(MainWindow mainWindow) {
	super(mainWindow);
        setName("Copy to clipboard");
        setTooltip("Copy a selected sequent term into your default clipboard.\n" +
        		"This functionality may depend on your window manager or installed clipboard managers.\n" +
        		"The default clipboard is not the 'middle click clipboard' on X window systems.");
    }
    
    @Override
    public void actionPerformed(ActionEvent e) {
        CurrentGoalView goalView = mainWindow.getGoalView();
        if (goalView == null) return;
        PosInSequent pis = goalView.getMousePosInSequent();
        if (pis == null) return;
        String s = goalView.getHighlightedText(pis);
        java.awt.datatransfer.StringSelection ss = 
                new java.awt.datatransfer.StringSelection(s);
        java.awt.Toolkit toolkit = Toolkit.getDefaultToolkit();
        toolkit.getSystemClipboard().setContents(ss, ss);
    }
}