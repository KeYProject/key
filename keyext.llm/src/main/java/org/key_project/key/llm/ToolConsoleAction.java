/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;

import org.key_project.key.llm.mcp.BuiltInMCPClient;

import org.jspecify.annotations.Nullable;

/**
 * Menu action that opens the non-modal {@link ToolConsoleDialog} for manually calling the agent
 * tools against the live environment (manual end-to-end testing). The dialog is created once per
 * action and reused; it uses the production {@link BuiltInMCPClient}, so approvals are shared
 * with the agent chat.
 *
 * @author Alexander Weigl
 */
class ToolConsoleAction extends MainWindowAction {

    /** The lazily created console dialog ({@code null} until the first invocation). */
    private @Nullable ToolConsoleDialog dialog;

    protected ToolConsoleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Tool Console…");
        setMenuPath("Proof.LLM");
        setTooltip("Manually call the agent tools against the current proof and settings"
            + " (interactive end-to-end testing)");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (dialog == null) {
            dialog = new ToolConsoleDialog(mainWindow, new BuiltInMCPClient());
        }
        dialog.setVisible(true);
        dialog.toFront();
    }
}
