/*
 * Created on 30.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * This notification task is used to inform the user about a non-error
 * situation (e.g. statistics (how many goals have been closed) etc.) 
 * @author bubel
 */
public class GeneralInformationNotification extends NotificationTask {

     
    /**
     * @see NotificationTask#executeImpl(NotificationEvent, NotificationManager)      
     */
    protected void executeImpl(NotificationEvent event,
            NotificationManager manager) {
        for (final NotificationAction action : getNotificationActions()) {         
            action.execute(event);
        }
    }

    /** 
     * @return the event id of a general information event
     * @see NotificationEventID
     */
    public int getEventID() {
        return NotificationEventID.GENERAL_INFORMATION;
    }

}
