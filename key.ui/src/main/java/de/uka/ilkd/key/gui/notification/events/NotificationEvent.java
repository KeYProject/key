/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * A NotificationEvent is triggered if the system wants to notify the user about a certain
 * situation. Each kind of event is assigned a unique id which are declared in
 * {@link de.uka.ilkd.key.gui.notification.NotificationEventID}.
 *
 * @author bubel
 */
public abstract class NotificationEvent {

    /** the unique id identifying the kind of this event */
    private final NotificationEventID eventID;

    /**
     * creates an instance of this event
     *
     * @param eventID the int identifying the kind of this event
     * @see NotificationEventID
     */
    public NotificationEvent(NotificationEventID eventID) {
        this.eventID = eventID;
    }

    /**
     * @return returns the eventID
     * @see NotificationEventID
     */
    public NotificationEventID getEventID() {
        return eventID;
    }

}
