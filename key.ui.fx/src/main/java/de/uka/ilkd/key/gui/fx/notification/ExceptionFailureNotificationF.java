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
 * TODO-merge (seam agent, branch {@code weigl/ocfx-seam}): exception routing (the Swing
 * {@code mediator.notify(new ExceptionFailureEvent(...))} call sites and the exception-dialog
 * path) is owned by the exception-seam agent; this task ships with the ERROR-toast action only
 * and is not wired into any control construction yet — it is exercised by the
 * {@code key.fx.verify.notifications} self-test hook. Runs also during auto mode (Swing parity).
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
