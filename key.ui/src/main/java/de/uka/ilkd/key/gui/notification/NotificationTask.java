/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification;

import java.util.ArrayList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * A notification task maps a {@link de.uka.ilkd.key.gui.notification.events.NotificationEvent} to a
 * list of actions to be performed when the event is encountered.
 *
 * @author bubel
 */
public abstract class NotificationTask {

    /**
     * the list of actions associated with this task
     */
    private final List<NotificationAction> notificationActions =
        new ArrayList<>(5);

    /**
     * @return returns the notification actions belonging to this task
     */
    public List<NotificationAction> getNotificationActions() {
        return notificationActions;
    }

    /**
     * adds an notificatin action this task.
     *
     * @param action the NotificationAction to be added
     */
    public void addNotificationAction(NotificationAction action) {
        this.notificationActions.add(action);
    }

    /**
     *
     * called to execute the notification task, but this method only takes care that we are in the
     * even dispatcher thread
     *
     * @param event the NotificationEvent triggering this task
     * @param manager the NotificationManager to which this tasks belongs to
     */
    public void execute(NotificationEvent event, NotificationManager manager) {
        // if we are in automode execute task only if it is
        // automode enabled
        if (manager.inAutoMode() && !automodeEnabledTask()) {
            return;
        }
        // notify thread safe
        if (SwingUtilities.isEventDispatchThread()) {
            executeActions(event, manager);
        } else {
            final NotificationEvent eventObject = event;
            final NotificationManager notManager = manager;
            SwingUtilities.invokeLater(() -> executeActions(eventObject, notManager));
        }
    }


    /**
     *
     * called to execute the notification task
     *
     * @param manager the NotificationManager to which this tasks belongs to
     * @param event the NotificationEvent triggering this task
     */
    protected void executeActions(NotificationEvent event, NotificationManager manager) {
        for (final NotificationAction action : getNotificationActions()) {
            action.execute(event);
        }
    }

    /**
     * @return the event if of this task
     */
    public abstract NotificationEventID getEventID();

    /**
     * returns if this task should be executed in auto mode
     *
     * @return if true execute task even if in automode
     */
    protected boolean automodeEnabledTask() {
        return false;
    }
}
