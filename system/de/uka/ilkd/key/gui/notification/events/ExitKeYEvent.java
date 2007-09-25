/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * An exit key event indicating that KeY is currently shut down.
 * @author bubel
 */
public class ExitKeYEvent extends NotificationEvent {

    /**
     * creates an event fired when KeY is shutdown
     */
    public ExitKeYEvent() {
        super(NotificationEventID.EXIT_KEY);      
    }

}
