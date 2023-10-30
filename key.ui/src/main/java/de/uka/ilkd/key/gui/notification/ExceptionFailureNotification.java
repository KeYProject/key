/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification;

import java.awt.Frame;

import de.uka.ilkd.key.gui.notification.actions.ExceptionFailureNotificationDialog;

public class ExceptionFailureNotification extends NotificationTask {

    public ExceptionFailureNotification(Frame parentComponent) {
        addNotificationAction(new ExceptionFailureNotificationDialog(parentComponent));
    }

    /**
     * returns if this task should be executed in auto mode
     *
     * @return if true execute task even if in automode
     */
    @Override
    protected boolean automodeEnabledTask() {
        return true;
    }

    @Override
    public NotificationEventID getEventID() {
        return NotificationEventID.EXCEPTION_CAUSED_FAILURE;
    }

}
