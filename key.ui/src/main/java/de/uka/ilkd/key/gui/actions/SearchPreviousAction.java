/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;


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
