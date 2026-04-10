/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.nodeviews.SequentViewSearchBar;


/*
 * Menu option for showing the next search result Keyboard shortcut: F3. This shortcut is set in the
 * KeyStrokemanager
 */
public class SearchPreviousAction extends MainWindowAction {

    private static final long serialVersionUID = -9002009635814787502L;
    private final SequentViewSearchBar searchBar;

    public SearchPreviousAction(MainWindow mainWindow, SequentViewSearchBar searchBar) {
        super(mainWindow);
        setName("Find Previous Occurrence");
        setIcon(IconFactory.SEARCH_PREV.get(16));
        setTooltip("Find the previous occurrence of current search term in sequent.");
        getMediator().enableWhenProofLoaded(this);

        this.searchBar = searchBar;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        searchBar.searchPrevious();
    }
}
