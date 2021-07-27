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

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import java.awt.event.ActionEvent;


/*
 * Menu option for showing the next search result
 * Keyboard shortcut: F3. This shortcut is set in the KeyStrokemanager
 */
public class SearchPreviousAction extends MainWindowAction {

    private static final long serialVersionUID = -9002009635814787502L;

    public SearchPreviousAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Find Previous Occurrence");
        setIcon(IconFactory.SEARCH_PREV.get(16));
        setTooltip("Find the previous occurrence of current search term in sequent.");
        getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        mainWindow.sequentViewSearchBar.searchPrevious();
    }
}
