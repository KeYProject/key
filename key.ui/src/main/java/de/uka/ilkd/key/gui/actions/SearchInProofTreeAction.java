/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import org.jspecify.annotations.NullMarked;

/*
 * Menu option for showing the proof tree search bar. Keyboard shortcut: STRG+SHIFT+F.
 */

@NullMarked
public class SearchInProofTreeAction extends MainWindowAction {

    private static final long serialVersionUID = -3317991560912504404L;

    /**
     * The action-configuration calls and the {@code enableWhenProofLoaded(this)} registration
     * operate on {@code this} while the receiver is still under initialization (EISOP
     * initialization check); safe here since the listener only reacts to later selection events,
     * suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:method.invocation.invalid",
        "nullness:argument.type.incompatible" })
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
