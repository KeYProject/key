/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.notification;

import org.jspecify.annotations.NullMarked;

/**
 * Notifies the user when a proof task is abandoned.
 *
 * @author bubel
 */
@NullMarked
public class AbandonNotification extends NotificationTask {

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.gui.notification.NotificationTask#getEventID()
     */
    @Override
    public NotificationEventID getEventID() {
        return NotificationEventID.TASK_ABANDONED;
    }

}
