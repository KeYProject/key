/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.notification;

import java.awt.Frame;

import de.uka.ilkd.key.gui.notification.actions.ExceptionFailureNotificationDialog;

import org.jspecify.annotations.NullMarked;

@NullMarked
public class ExceptionFailureNotification extends NotificationTask {

    /**
     * Creates the exception-failure notification task.
     *
     * <p>
     * The task registers its notification action while the receiver is still under initialization
     * (EISOP initialization check); the action only fires once the task is executed after
     * construction, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
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
