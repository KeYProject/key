/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

import de.uka.ilkd.key.gui.fx.notification.actions.ToastActionF;

/**
 * This notification task is used to inform the user about a non-error situation (e.g.
 * statistics (how many goals have been closed) etc.).
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * GeneralInformationNotification.java} (Swing action: {@code GeneralInformationJTextPaneDisplay},
 * a modal information dialog; FX deviation: INFO toast).
 */
public class GeneralInformationNotificationF extends NotificationTaskF {

    /**
     * creates the notification task
     */
    public GeneralInformationNotificationF() {
        addNotificationAction(new ToastActionF());
    }

    @Override
    public NotificationEventIDF getEventID() {
        return NotificationEventIDF.GENERAL_INFORMATION;
    }
}
