/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * An exit key event indicating that KeY is currently shut down.
 *
 * @author bubel
 */
public class ExitKeYEvent extends NotificationEvent {

    /**
     * creates an event fired when KeY is shutdown
     */
    public ExitKeYEvent() {
        super(NotificationEventID.EXIT_KEY);
    }

}
