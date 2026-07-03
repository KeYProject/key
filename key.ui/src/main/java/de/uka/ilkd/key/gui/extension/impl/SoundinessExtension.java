/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.impl;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ShowSoundinessAction;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.proof.Proof;

/**
 * Extension that adds soundiness report functionality to the UI.
 * Adds context menu item to proof list and enables soundiness analysis.
 * 
 * @author opencode
 * @since 2.13
 */
@KeYGuiExtension.Info(
    name = "Soundiness Report",
    description = "Provides soundiness analysis for proofs showing assumptions, unsound choices, and verification limitations.",
    experimental = false,
    optional = true,
    priority = 1000
)
public class SoundinessExtension implements KeYGuiExtension, KeYGuiExtension.ContextMenu {
    
    @Override
    public <T> List<javax.swing.Action> getContextActions(KeYMediator mediator, ContextMenuKind<T> kind, T underlyingObject) {
        List<javax.swing.Action> actions = new ArrayList<>();
        
        // Add to proof list context menu
        if (kind == ContextMenuKind.PROOF_LIST && underlyingObject instanceof Proof) {
            MainWindow mainWindow = MainWindow.getInstance();
            if (mainWindow != null) {
                actions.add(new ShowSoundinessAction(mainWindow));
            }
        }
        
        return actions;
    }
}
