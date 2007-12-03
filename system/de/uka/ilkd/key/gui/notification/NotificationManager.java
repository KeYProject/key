/*
 * Created on 17.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.notification.actions.*;
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
    private List notificationTasks = new ArrayList();
    
    /** true if we are currently in automode */
    private boolean automode;
    
    private KeYMediator mediator;
    
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
    
    
    /**
     * %%HACK: move these methods
     * set default with or without sound
     */
    public void setDefaultNotification(boolean sound) {
       
        notificationTasks.clear();
        
        final ProofClosedNotification pcn = new ProofClosedNotification();
        final GeneralFailureNotification gfn = new GeneralFailureNotification();
        final GeneralInformationNotification gin = 
            new GeneralInformationNotification();
        final AbandonNotification an = new AbandonNotification();
        final ExitKeYNotification en = new ExitKeYNotification();

        if (sound) {            
            pcn.addNotificationAction(new ProofClosedSoundPlay());                                     
            gfn.addNotificationAction(new GeneralFailureSoundPlay());            
            gin.addNotificationAction(new GeneralInformationSoundPlay());
            an.addNotificationAction(new AbandonTaskSoundPlay());                      
            en.addNotificationAction(new ExitKeYSoundPlay());                 
        }
        
        gfn.addNotificationAction(new GeneralFailureJTextPaneDisplay(mediator.mainFrame()));
        gin.addNotificationAction(new GeneralInformationJTextPaneDisplay(mediator.mainFrame()));
        pcn.addNotificationAction(new ProofClosedJTextPaneDisplay(mediator.mainFrame()));
        
        addNotificationTask(pcn);
        addNotificationTask(gfn);
        addNotificationTask(gin);
        addNotificationTask(an);
        addNotificationTask(en);       
    }
    
    
    /**
     * creates an instance of the notification manager    
     */
    public NotificationManager(KeYMediator mediator) {        
        
        notificationListener = new NotificationListener();
        this.mediator = mediator;
        mediator.addAutoModeListener(notificationListener);         
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
    public Iterator getNotificationTasks() {
        return notificationTasks.iterator();
    }

    /**
     * find the notificatin task associated with the given event id
     * @param eventId int identifying the event
     * @return the notificatin task associated with the given event id
     */
    private NotificationTask getNotificationTask(int eventId) {
        final Iterator it = getNotificationTasks();
        while (it.hasNext()) {
            final NotificationTask task = (NotificationTask)it.next();
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
     * dispatches the received notification event an triggers
     * the corresponding task
     * @param event
     */
    public void notify(NotificationEvent event) {
        getNotificationTask(event.getEventID()).
        execute(event, NotificationManager.this);        
    }
    
}

