/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * Emitted after removing a proof task
 * @author bubel
 */
public class AbandonTaskEvent extends NotificationEvent {

    /**
     * creates an event
     */
    public AbandonTaskEvent() {
        super(NotificationEventID.TASK_ABANDONED);        
    }

}
