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
import de.uka.ilkd.key.gui.MainWindow;

/*
 * Menu option for showing the proof tree search bar.
 * Keyboard shortcut: STRG+SHIFT+F.
 */

public class SearchInProofTreeAction extends MainWindowAction {

    private static final long serialVersionUID = -3317991560912504404L;

    public SearchInProofTreeAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Search in proof tree");
        setTooltip("Search for rule names or node numbers in the proof tree.");
        
        this.setAcceleratorKey(
                de.uka.ilkd.key.gui.prooftree.ProofTreeView.searchKeyStroke);
        getMediator().enableWhenProofLoaded(this);
        
    }

    @Override
    public void actionPerformed(ActionEvent arg0) {
        mainWindow.selectTab(0);
        mainWindow.getProofView().showSearchPanel();
    }
}
