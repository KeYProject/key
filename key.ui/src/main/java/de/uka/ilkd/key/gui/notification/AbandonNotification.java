/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification;

/**
 * Notifies the user when a proof task is abandoned.
 *
 * @author bubel
 */
public class AbandonNotification extends NotificationTask {

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.gui.notification.NotificationTask#getEventID()
     */
    @Override
    public NotificationEventID getEventID() {
        return NotificationEventID.TASK_ABANDONED;
    }

}
