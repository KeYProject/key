/*
 * Created on 03.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * this interface is implemented by notification actions 
 * @author bubel
 */
public interface NotificationAction {

    /**
     * executes the action
     * @param event the NotificationEvent triggering this action 
     * @return indicator if action has been executed successfully     
     */
    boolean execute(NotificationEvent event);
}
