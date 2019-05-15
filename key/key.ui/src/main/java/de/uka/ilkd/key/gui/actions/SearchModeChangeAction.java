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

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.SequentViewSearchBar;


/*
 * Menu option for showing the next search result of sequent search
 * Keyboard shortcut: F3. This shortcut is set in the KeyStrokemanager
 */
public class SearchModeChangeAction extends MainWindowAction {

    private static final long serialVersionUID = -9002019635814787502L;
    private final SequentViewSearchBar.SearchMode mode;

    public SearchModeChangeAction(MainWindow mainWindow, SequentViewSearchBar.SearchMode mode) {
        super(mainWindow);
        setName(mode.toString());

        setIcon(
            mode.icon
        );
        setTooltip("Find the next occurence of current search term in sequent.");
        getMediator().enableWhenProofLoaded(this);
	    if(mode == SequentViewSearchBar.SearchMode.HIGHLIGHT) {
            setAcceleratorLetter(KeyEvent.VK_H);
        } else if (mode == SequentViewSearchBar.SearchMode.HIDE) {
            setAcceleratorLetter(KeyEvent.VK_ESCAPE);
        } else if (mode == SequentViewSearchBar.SearchMode.REGROUP) {
            setAcceleratorLetter(KeyEvent.VK_I);
        }
        
        this.mode = mode;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        mainWindow.sequentViewSearchBar.setSearchMode(mode);
    }
}
