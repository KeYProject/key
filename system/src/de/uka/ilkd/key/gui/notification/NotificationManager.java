// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


/*
 * Created on 17.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import javax.swing.JFrame;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.notification.actions.ExceptionFailureNotificationDialog;
import de.uka.ilkd.key.gui.notification.actions.GeneralFailureJTextPaneDisplay;
import de.uka.ilkd.key.gui.notification.actions.GeneralInformationJTextPaneDisplay;
import de.uka.ilkd.key.gui.notification.actions.ProofClosedJTextPaneDisplay;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.proof.ProofEvent;


/**
 * The notificatin manager controls the list of active 
 * notification tasks. It receives KeY System events and looks 
 * for an appropriate task   
 * @author bubel
 */
public class NotificationManager {

    /** list of notification tasks */
    private List<NotificationTask> notificationTasks = new ArrayList<NotificationTask>();
    
    /** true if we are currently in automode */
    private boolean automode;
        
    // Dummy task to avoid null pointer checks
    private static final NotificationTask DUMMY_TASK = 
        new NotificationTask() {
        
        protected void executeImpl(NotificationEvent event, 
                NotificationManager manager) {                     
        }

        public int getEventID() {           
            return NotificationEventID.RESERVED;
        }
    };

    private NotificationListener notificationListener;
    
    

    public void setDefaultNotification(JFrame comp) {
       
        notificationTasks.clear();
        
        final ProofClosedNotification pcn = new ProofClosedNotification();
        final ExceptionFailureNotification efn = new ExceptionFailureNotification();
        final GeneralFailureNotification gfn = new GeneralFailureNotification();
        final GeneralInformationNotification gin = 
            new GeneralInformationNotification();
        final AbandonNotification an = new AbandonNotification();
        final ExitKeYNotification en = new ExitKeYNotification();
        
        gfn.addNotificationAction(new GeneralFailureJTextPaneDisplay(comp));
        gin.addNotificationAction(new GeneralInformationJTextPaneDisplay(comp));
        pcn.addNotificationAction(new ProofClosedJTextPaneDisplay(comp));
        efn.addNotificationAction(new ExceptionFailureNotificationDialog(comp));
        
        addNotificationTask(pcn);
        addNotificationTask(gfn);
        addNotificationTask(gin);
        addNotificationTask(an);
        addNotificationTask(en);       
    }
    
    
    /**
     * creates an instance of the notification manager    
     */
    public NotificationManager(KeYMediator mediator, JFrame comp) {        
        
        notificationListener = new NotificationListener();
        mediator.addAutoModeListener(notificationListener);
        setDefaultNotification(comp);
    }
    
            
    /**
     * adds a notification task to this manager     
     * @param task the NotificationTask to be added
     */
    public void addNotificationTask(NotificationTask task) {	
        notificationTasks.add(task);
    }
    
    /**
     * removes the given notification task from the list of active
     * tasks
     * @param task the task to be removed 
     */
    public void removeNotificationTask(NotificationTask task) {
        notificationTasks.remove(task);
    }
    
    /**
     * returns the registered notifications
     * @return the registered notifications
     */
    public Iterator<NotificationTask> getNotificationTasks() {
        return notificationTasks.iterator();
    }

    /**
     * find the notification task associated with the given event id
     * @param eventId int identifying the event
     * @return the notification task associated with the given event id
     */
    public NotificationTask getNotificationTask(int eventId) {
        final Iterator<NotificationTask> it = getNotificationTasks();
        while (it.hasNext()) {
            final NotificationTask task = it.next();
            if (task.getEventID() == eventId) {
                return task;
            }
        }
        return DUMMY_TASK;
    }
    
    /**
     * @return true if the prover is currently in automode
     */
    public boolean inAutoMode() {       
        return automode;
    }
    
    // Listener section with inner classes used to receive 
    // KeY system events
    private class NotificationListener implements AutoModeListener {
         
        /**
         * auto mode started
         */
        public void autoModeStarted(ProofEvent e) {
            automode = true;          
        }

        /**
         * auto mode stopped
         */
        public void autoModeStopped(ProofEvent e) {                        
            automode = false;
        }
                        
    }

    /**
     * dispatches the received notification event and triggers
     * the corresponding task
     * @param event
     */
    public void notify(NotificationEvent event) {
        getNotificationTask(event.getEventID()).
        execute(event, NotificationManager.this);        
    }
    
}

