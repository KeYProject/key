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

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.IncrementalSearch;
import de.uka.ilkd.key.gui.nodeviews.SequentView;

public class SearchInSequentAction extends MainWindowAction {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public SearchInSequentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Search in sequent view");
        setTooltip("Search for strings in the current sequent.");
        this.setAcceleratorKey(KeyStroke.getKeyStroke(KeyEvent.VK_F3,0));
        
        getMediator().enableWhenProof(this);
    }
	
	@Override
    public void actionPerformed(ActionEvent e) {
		if (mainWindow.getMediator().getProof() != null) {
			SequentView seqView = mainWindow.getSequentView();
                        mainWindow.sequentSearchPanel.toggleVisibility();
			IncrementalSearch search = IncrementalSearch.getInstance();
            if (!search.isInitialised()) {
                search.initSearch(seqView);
            } else {
                search.requestFocus();
            }
		}
		
    }

}
