/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;

public class MenuSendFeedackAction extends MainWindowAction {

    private static final long serialVersionUID = 1L;

    public MenuSendFeedackAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Send Feedback...");
    }

    /**
     * Re-using {@link SendFeedbackAction} from {@link IssueDialog} for this.
     */
    private final SendFeedbackAction action = new SendFeedbackAction(mainWindow);

    @Override
    public void actionPerformed(ActionEvent arg0) {
        action.actionPerformed(arg0);
    }
}
