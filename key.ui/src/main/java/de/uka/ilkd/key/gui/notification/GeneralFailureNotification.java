/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification;

import javax.swing.JFrame;

import de.uka.ilkd.key.gui.notification.actions.GeneralFailureJTextPaneDisplay;

/**
 * This task notifies the user about an unexpected error.
 *
 * @author bubel
 */
public class GeneralFailureNotification extends NotificationTask {

    public GeneralFailureNotification(JFrame comp) {
        addNotificationAction(new GeneralFailureJTextPaneDisplay(comp));
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

    /**
     * @return the event id of a general failure event
     * @see NotificationEventID
     */
    @Override
    public NotificationEventID getEventID() {
        return NotificationEventID.GENERAL_FAILURE;
    }

}
