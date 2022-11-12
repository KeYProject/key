/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Frame;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

public class ExceptionFailureNotificationDialog extends ShowDisplayPane {

    public ExceptionFailureNotificationDialog(Frame parentComponent) {
        super(parentComponent);
    }

    @Override
    public boolean execute(NotificationEvent event) {
        if (event instanceof ExceptionFailureEvent) {
            ExceptionFailureEvent ev = (ExceptionFailureEvent) event;
            setMessage(ev.getErrorMessage());
            IssueDialog.showExceptionDialog(parentComponent, ev.getException());
        } else {
            setMessage("An unknown error has occured." + event);
            JOptionPane.showMessageDialog(parentComponent, getMessage(), "Error",
                    JOptionPane.ERROR_MESSAGE);
        }
        return true;
    }

}
