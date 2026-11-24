/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

import de.uka.ilkd.key.gui.fx.notification.events.NotificationEventF;

/**
 * This interface is implemented by notification actions.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * NotificationAction.java}.
 */
public interface NotificationActionF {

    /**
     * executes the action
     *
     * @param event the NotificationEvent triggering this action
     * @return indicator if action has been executed successfully
     */
    boolean execute(NotificationEventF event);
}
