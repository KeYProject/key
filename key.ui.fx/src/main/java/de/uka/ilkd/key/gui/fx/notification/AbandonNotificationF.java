/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

/**
 * Notifies the user when a proof task is abandoned.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * AbandonNotification.java}, which declares no actions (the Swing manager only keeps the task
 * registered so that callers can add their own actions, e.g. the Eclipse integration).
 */
public class AbandonNotificationF extends NotificationTaskF {

    @Override
    public NotificationEventIDF getEventID() {
        return NotificationEventIDF.TASK_ABANDONED;
    }
}
