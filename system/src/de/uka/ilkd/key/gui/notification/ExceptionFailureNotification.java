package de.uka.ilkd.key.gui.notification;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

public class ExceptionFailureNotification extends NotificationTask {

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

	@Override
	public int getEventID() {
		return NotificationEventID.EXCEPTION_CAUSED_FAILURE;
	}

}
