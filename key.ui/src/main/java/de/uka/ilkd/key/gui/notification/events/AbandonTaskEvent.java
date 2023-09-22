/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * Emitted after removing a proof task
 *
 * @author bubel
 */
public class AbandonTaskEvent extends NotificationEvent {

    /**
     * creates an event
     */
    public AbandonTaskEvent() {
        super(NotificationEventID.TASK_ABANDONED);
    }

}
