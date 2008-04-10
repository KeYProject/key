/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * Notifies the user when a proof task is abandoned.
 * @author bubel
 */
public class AbandonNotification extends NotificationTask {

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.notification.NotificationTask#executeImpl(de.uka.ilkd.key.gui.notification.NotificationEvent, de.uka.ilkd.key.gui.notification.NotificationManager)
     */
    protected void executeImpl(NotificationEvent event,
            NotificationManager manager) {
        for (final NotificationAction action : getNotificationActions()) {         
            action.execute(event);
        }
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.notification.NotificationTask#getEventID()
     */
    public int getEventID() {
        return NotificationEventID.TASK_ABANDONED;
    }

}
