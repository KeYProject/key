/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import org.jspecify.annotations.NullMarked;

/// Menu option for selecting the proof node with the given node number.
///
/// Keyboard shortcut: Ctrl + G (see {@link de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeSettings})
///
/// @author Wolfram Pfeifer
@NullMarked
public class GotoNodeAction extends MainWindowAction {

    /**
     * The action-configuration calls and the {@code enableWhenProofLoaded(this)} registration
     * operate on {@code this} while the receiver is still under initialization (EISOP
     * initialization check); safe here since the listener only reacts to later selection events,
     * suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:method.invocation.invalid",
        "nullness:argument.type.incompatible" })
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
