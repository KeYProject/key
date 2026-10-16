/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

/// Menu option for selecting the proof node with the given node number.
///
/// Keyboard shortcut: Ctrl + G (see {@link de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeSettings})
///
/// @author Wolfram Pfeifer
public class GotoNodeAction extends MainWindowAction {

    public GotoNodeAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Go to Node...");
        setIcon(IconFactory.GOTO_NODE.get(IconFactory.DEFAULT_SIZE));
        setTooltip("Go to the proof node with the given node number.");
        getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent arg0) {
        mainWindow.getProofTreeView().showGotoNodeDialog();
    }
}
