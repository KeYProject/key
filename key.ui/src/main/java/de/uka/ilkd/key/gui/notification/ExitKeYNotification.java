/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification;

import java.lang.reflect.InvocationTargetException;
import javax.swing.*;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This task takes care for a notification when exiting KeY.
 *
 * @author bubel
 */
public class ExitKeYNotification extends NotificationTask {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExitKeYNotification.class);

    /**
     * overwritten as invokeAndWait is taken called to execute the notification task, but this
     * method only takes care that we are in the even dispatcher thread
     *
     * @param manager the NotificationManager to which this tasks belongs to
     * @param event the NotificationEvent triggering this task
     */
    @Override
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
            try {
                SwingUtilities.invokeAndWait(() -> executeActions(eventObject, notManager));
            } catch (InterruptedException | InvocationTargetException e) {
                LOGGER.debug("unexpected exception during notification");
            }
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.gui.notification.NotificationTask#getEventID()
     */
    @Override
    public NotificationEventID getEventID() {
        return NotificationEventID.EXIT_KEY;
    }

}
