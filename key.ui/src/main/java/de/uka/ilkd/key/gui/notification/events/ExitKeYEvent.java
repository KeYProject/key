/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
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
