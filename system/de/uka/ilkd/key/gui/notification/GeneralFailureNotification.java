/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * This task notifies the user about an unexpected error.
 * @author bubel
 */
public class GeneralFailureNotification extends NotificationTask {

    /**
     * returns if this task should be executed in auto mode
     * @return if true execute task even if in automode
     */
    protected boolean automodeEnabledTask() {   
        return true;
    }
    
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
     * @return the event id of a general failure event
     * @see NotificationEventID
     */
    public int getEventID() {
        return NotificationEventID.GENERAL_FAILURE;
    }

}
