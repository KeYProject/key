/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

import de.uka.ilkd.key.gui.fx.notification.actions.ToastActionF;

/**
 * This task notifies the user about an unexpected error.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * GeneralFailureNotification.java} (Swing action: {@code GeneralFailureJTextPaneDisplay}, a
 * modal error dialog; FX deviation: ERROR toast). Runs also during auto mode.
 */
public class GeneralFailureNotificationF extends NotificationTaskF {

    /**
     * creates the notification task
     */
    public GeneralFailureNotificationF() {
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
        return NotificationEventIDF.GENERAL_FAILURE;
    }
}
