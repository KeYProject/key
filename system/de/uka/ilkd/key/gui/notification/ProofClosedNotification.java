/*
 * Created on 17.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * The proof closed notification notifies the user about a successful attempt 
 * closing a proof. 
 * @author bubel
 */
public class ProofClosedNotification extends NotificationTask {

    
    /**
     * Creates a proof closed notification task.     
     */
    public ProofClosedNotification() {       
    }

    /**
     * returns if this task should be executed in auto mode
     * @return if true execute task even if in automode
     */
    protected boolean automodeEnabledTask() {   
        return true;
    }
    
    /**
     * @return the event if of this task
     */
    public int getEventID() {       
        return NotificationEventID.PROOF_CLOSED;
    }     
    
    /**
     * executes the proof closed notification task
     */
    public void executeImpl (NotificationEvent event, NotificationManager manager) {
        for (final NotificationAction action : getNotificationActions()) {         
            action.execute(event);
        }
   }
}
