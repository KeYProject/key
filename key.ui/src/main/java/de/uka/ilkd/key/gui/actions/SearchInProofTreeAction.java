/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

/*
 * Menu option for showing the proof tree search bar. Keyboard shortcut: STRG+SHIFT+F.
 */

public class SearchInProofTreeAction extends MainWindowAction {

    private static final long serialVersionUID = -3317991560912504404L;

    public SearchInProofTreeAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Search in Proof Tree");
        setIcon(IconFactory.search2(16));
        setTooltip("Search for rule names or node numbers in the proof tree.");

        setAcceleratorKey(de.uka.ilkd.key.gui.prooftree.ProofTreeView.SEARCH_KEY_STROKE);
        getMediator().enableWhenProofLoaded(this);

    }

    @Override
    public void actionPerformed(ActionEvent arg0) {
        mainWindow.getProofTreeView().showSearchPanel();
    }
}
