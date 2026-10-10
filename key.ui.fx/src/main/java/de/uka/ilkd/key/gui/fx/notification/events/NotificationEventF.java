/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification.events;

import de.uka.ilkd.key.gui.fx.notification.NotificationEventIDF;

/**
 * A {@code NotificationEventF} is triggered if the system wants to notify the user about a
 * certain situation. Each kind of event is assigned a unique id which is declared in
 * {@link NotificationEventIDF}.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * events/NotificationEvent.java}.
 */
public abstract class NotificationEventF {

    /** the unique id identifying the kind of this event */
    private final NotificationEventIDF eventID;

    /**
     * creates an instance of this event
     *
     * @param eventID the id identifying the kind of this event
     * @see NotificationEventIDF
     */
    protected NotificationEventF(NotificationEventIDF eventID) {
        this.eventID = eventID;
    }

    /**
     * @return returns the eventID
     * @see NotificationEventIDF
     */
    public NotificationEventIDF getEventID() {
        return eventID;
    }
}
