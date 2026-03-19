/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * this interface is implemented by notification actions
 *
 * @author bubel
 */
public interface NotificationAction {

    /**
     * executes the action
     *
     * @param event the NotificationEvent triggering this action
     * @return indicator if action has been executed successfully
     */
    boolean execute(NotificationEvent event);
}
