/*
 * Created on 3.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * A notification task maps a 
 * {@link de.uka.ilkd.key.gui.notification.events.NotificationEvent} to a list 
 * of actions to be performed when the event is encountered.
 * @author bubel
 */
public abstract class NotificationTask {
    
    /**
     *  the list of actions associated with this task
     */
    private List notificationActions = new ArrayList(5);
            
    /**
     * @return returns the notification actions belonging to 
     * this task
     */
    public List getNotificationActions() {
        return notificationActions;
    }
    
    /**
     * adds an notificatin action this task. 
     * @param action the NotificationAction to be added  
     */
    public void addNotificationAction(NotificationAction action) {
        this.notificationActions.add(action);
    }
   

    /**
     * @return an iterator about the registered actions
     */
    public Iterator getActions() {   
        return notificationActions.iterator();
    }
    
    /**
     * 
     * called to execute the notification task, but this method
     * only takes care that we are in the even dispatcher thread
     * @param event the NotificationEvent triggering this task
     * @param manager the NotificationManager to which this 
     * tasks belongs to
     */
    public void execute(NotificationEvent event, 
            NotificationManager manager) {      
        // if we are in automode execute task only if it is 
        // automode enabled
        if (manager.inAutoMode() && !automodeEnabledTask()) {
            return;
        }
        // notify thread safe
        if (SwingUtilities.isEventDispatchThread()) {
            executeImpl(event, manager);
        } else {
            final NotificationEvent eventObject = event;
            final NotificationManager notManager = manager;
            SwingUtilities.invokeLater(new Runnable() {                                    
                public void run() {                
                    executeImpl(eventObject, notManager);
                }               
            });
        }
    }


    /**
    
     * called to execute the notification task
     * @param manager the NotificationManager to which this 
     * tasks belongs to
     * @param event the NotificationEvent triggering this task
     */
    protected abstract void executeImpl(NotificationEvent event, 
            NotificationManager manager);
    
    /**
     * @return the event if of this task
     */
    public abstract int getEventID(); 

    /**
     * returns if this task should be executed in auto mode
     * @return if true execute task even if in automode
     */
    protected boolean automodeEnabledTask() {   
        return false;
    }
}
