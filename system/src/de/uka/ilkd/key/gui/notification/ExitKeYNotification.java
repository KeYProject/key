// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import java.lang.reflect.InvocationTargetException;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.util.Debug;

/**
 * This task takes care for a notification when exiting KeY. 
 * @author bubel
 */
public class ExitKeYNotification extends NotificationTask {

    
    /**
     * overwritten as invokeAndWait is taken 
     * called to execute the notification task, but this method
     * only takes care that we are in the even dispatcher thread
     * @param manager the NotificationManager to which this 
     * tasks belongs to
     * @param event the NotificationEvent triggering this task
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
           try {
            SwingUtilities.invokeAndWait(new Runnable() {                                    
                public void run() {                
                    executeImpl(eventObject, notManager);		   
                }               
               });
           } catch (InterruptedException e) {
               Debug.out("unexpected exception during notification");
           } catch (InvocationTargetException e) {
               Debug.out("unexpected exception during notification");
           }
	}
    }
    /**
     * executes the actions of this task
     */
    protected void executeImpl(NotificationEvent event,
            NotificationManager manager) {
        for (final NotificationAction action : getNotificationActions()) {                    
            action.execute(event);
        }
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.notification.NotificationTask#getEventID()
     */
    public int getEventID() {
        return NotificationEventID.EXIT_KEY;
    }

}