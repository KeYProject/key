/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

import de.uka.ilkd.key.gui.fx.notification.actions.ToastActionF;

/**
 * This task notifies the user about an exception causing a failure.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * ExceptionFailureNotification.java} (Swing action:
 * {@code ExceptionFailureNotificationDialog} → {@code IssueDialog.showExceptionDialog}).
 * <p>
 * termmenu/S4: this task is a default registration of {@code NotificationCenterF}
 * ({@code setDefaultNotifications}) and receives the exception events fired by the
 * application — e.g. the load-failure path {@code MainWindowF.setOnFailed} routes its
 * {@code ExceptionFailureEventF} through the center. Deviation from the Swing original,
 * which is why the Swing FIXME (double dialog for parser errors) does not apply: the action
 * is a toast, not a dialog ({@link ToastActionF}); the IssueDialog stays the primary
 * surface of the reporting exception path. Runs also during auto mode (Swing parity).
 */
public class ExceptionFailureNotificationF extends NotificationTaskF {

    /**
     * creates the notification task with the toast display action
     */
    public ExceptionFailureNotificationF() {
        addNotificationAction(new ToastActionF());
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
    public NotificationEventIDF getEventID() {
        return NotificationEventIDF.EXCEPTION_CAUSED_FAILURE;
    }
}
