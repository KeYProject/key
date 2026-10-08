/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

import java.util.ArrayList;
import java.util.List;
import javafx.application.Platform;

import de.uka.ilkd.key.gui.fx.notification.events.NotificationEventF;

/**
 * A notification task maps a {@link NotificationEventF} to a list of actions to be performed
 * when the event is encountered.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * NotificationTask.java}. The EDT marshalling via {@code SwingUtilities.invokeLater}
 * (NotificationTask.java:63) maps to {@link Platform#runLater(Runnable)}; like Swing, actions
 * already invoked on the FX application thread run synchronously.
 */
public abstract class NotificationTaskF {

    /**
     * the list of actions associated with this task
     */
    private final List<NotificationActionF> notificationActions = new ArrayList<>(5);

    /**
     * @return returns the notification actions belonging to this task
     */
    public List<NotificationActionF> getNotificationActions() {
        return notificationActions;
    }

    /**
     * adds a notification action to this task.
     *
     * @param action the NotificationActionF to be added
     */
    public void addNotificationAction(NotificationActionF action) {
        this.notificationActions.add(action);
    }

    /**
     * called to execute the notification task, but this method only takes care that we are on
     * the FX application thread
     *
     * @param event the NotificationEventF triggering this task
     * @param manager the NotificationCenterF to which this task belongs to
     */
    public void execute(NotificationEventF event, NotificationCenterF manager) {
        // if we are in automode execute task only if it is automode enabled
        if (manager.inAutoMode() && !automodeEnabledTask()) {
            return;
        }
        // notify thread safe
        if (Platform.isFxApplicationThread()) {
            executeActions(event, manager);
        } else {
            Platform.runLater(() -> executeActions(event, manager));
        }
    }

    /**
     * called to execute the notification task
     *
     * @param manager the NotificationCenterF to which this task belongs to
     * @param event the NotificationEventF triggering this task
     */
    protected void executeActions(NotificationEventF event, NotificationCenterF manager) {
        for (final NotificationActionF action : getNotificationActions()) {
            action.execute(event);
        }
    }

    /**
     * @return the event id of this task
     */
    public abstract NotificationEventIDF getEventID();

    /**
     * returns if this task should be executed in auto mode
     *
     * @return if true execute task even if in automode
     */
    protected boolean automodeEnabledTask() {
        return false;
    }
}
