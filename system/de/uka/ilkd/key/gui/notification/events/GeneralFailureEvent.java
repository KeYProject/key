/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * A notification event caused by a general unexpected failure
 * (usually caused by a bug of the system)
 * @author bubel
 */
public class GeneralFailureEvent extends NotificationEvent {

    private String errorMessage = "Unknown Error.";
    
    /**
     * creates an instance of this event
     * @param errorMessage a String describing the failure
     */
    public GeneralFailureEvent(String errorMessage) {
        super(NotificationEventID.GENERAL_FAILURE);
        this.errorMessage = errorMessage;
    }
    
    /**
     * @return the error message describing the reason for
     * this event    
     */
    public String getErrorMessage() {
        return errorMessage;
    }        
    
}
