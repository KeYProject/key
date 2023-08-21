/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Frame;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ExceptionFailureNotificationDialog extends ShowDisplayPane {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(ExceptionFailureNotificationDialog.class);

    public ExceptionFailureNotificationDialog(Frame parentComponent) {
        super(parentComponent);
    }

    @Override
    public boolean execute(NotificationEvent event) {
        if (event instanceof ExceptionFailureEvent) {
            ExceptionFailureEvent ev = (ExceptionFailureEvent) event;
            setMessage(ev.getErrorMessage());
            LOGGER.error(ev.getErrorMessage(), ev.getException());
            IssueDialog.showExceptionDialog(parentComponent, ev.getException());
        } else {
            setMessage("An unknown error has occured." + event);
            JOptionPane.showMessageDialog(parentComponent, getMessage(), "Error",
                JOptionPane.ERROR_MESSAGE);
        }
        return true;
    }

}
