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
import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import java.awt.Toolkit;

/*
 * Menu option for showing the sequent search bar.
 * Keyboard shortcut: STRG+F.
 */
public class SearchInSequentAction extends MainWindowAction {

    private static final long serialVersionUID = -9002009635814787502L;

    public SearchInSequentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Search in sequent view");
        setIcon(IconFactory.search(16));
        setTooltip("Search for strings in the current sequent.");
        // Key combination for this action: STRG+F.
        this.setAcceleratorKey(KeyStroke.getKeyStroke(KeyEvent.VK_F,
                Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        SequentView view = mainWindow.sequentViewSearchBar.getSequentView();
        String searchString = view.getHighlightedText();
        mainWindow.sequentViewSearchBar.searchField.setText(searchString);
        mainWindow.sequentViewSearchBar.setVisible(true);
        mainWindow.sequentViewSearchBar.search();
    }
}