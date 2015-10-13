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
 * Created on 17.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import java.util.EnumMap;
import java.util.Map;

import javax.swing.JFrame;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.proof.ProofEvent;

/**
 * The notificatin manager controls the list of active notification tasks. It
 * receives KeY System events and looks for an appropriate task
 * 
 * @author bubel
 */
public class NotificationManager {

   /** list of notification tasks */
   private Map<NotificationEventID, NotificationTask> notificationTasks = new EnumMap<NotificationEventID, NotificationTask>(
         NotificationEventID.class);

   /** true if we are currently in automode */
   private boolean autoMode = false;

   private NotificationListener notificationListener;

   public void setDefaultNotification(JFrame comp) {
      notificationTasks.clear();
      addNotificationTask(new ProofClosedNotification(comp));
      addNotificationTask(new GeneralFailureNotification(comp));
      addNotificationTask(new GeneralInformationNotification(comp));
      addNotificationTask(new AbandonNotification());
      addNotificationTask(new ExitKeYNotification());
      
      //FIXME (DS): Obviously, adding ExceptionFailureNotification at this\\
      // place leads to a double appearance of Dialogs in case of a parser\\
      // error. However, the user is not notified in case of an ExceptionFailure\\
      // occurring *after* the parsing procedure, so for instance at an\\
      // erroneous BuiltInRule application. This is not desirable, since\\
      // then there might be a strange GUI behavior without even a notification.
      // addNotificationTask(new ExceptionFailureNotification(comp));
   }

   /**
    * creates an instance of the notification manager
    */
   public NotificationManager(KeYMediator mediator, JFrame comp) {
      notificationListener = new NotificationListener();
      // This method delegates the request only to the UserInterfaceControl
      // which implements the functionality.
      // No functionality is allowed in this method body!
      mediator.getUI().getProofControl()
            .addAutoModeListener(notificationListener);
      setDefaultNotification(comp);
   }

   /**
    * adds a notification task to this manager
    * 
    * @param task
    *           the NotificationTask to be added
    */
   public void addNotificationTask(NotificationTask task) {
      notificationTasks.put(task.getEventID(), task);
   }

   /**
    * removes the given notification task from the list of active tasks
    * 
    * @param task
    *           the task to be removed
    */
   public void removeNotificationTask(NotificationTask task) {
      removeNotificationTask(task.getEventID());
   }
   
   /**
    * Removes the {@link NotificationTask} with the given {@link NotificationEventID}.
    * <p>
    * This functionality is used by the Eclipse integration.
    * @param eventID The {@link NotificationEventID} to remove its {@link NotificationTask}.
    * @return The removed {@link NotificationTask} or {@code null} if none was available.
    */
   public NotificationTask removeNotificationTask(NotificationEventID eventID) {
      return notificationTasks.remove(eventID);
   }

   /**
    * @return true if the prover is currently in automode
    */
   public boolean inAutoMode() {
      return autoMode;
   }

   // Listener section with inner classes used to receive
   // KeY system events
   private class NotificationListener implements AutoModeListener {

      /**
       * auto mode started
       */
      @Override
      public void autoModeStarted(ProofEvent e) {
         autoMode = true;
      }

      /**
       * auto mode stopped
       */
      @Override
      public void autoModeStopped(ProofEvent e) {
         autoMode = false;
      }

   }

   /**
    * dispatches the received notification event and triggers the corresponding
    * task
    * 
    * @param event
    */
   public void handleNotificationEvent(NotificationEvent event) {
      NotificationTask notificationTask = notificationTasks.get(event
            .getEventID());
      if (notificationTask != null) {
         notificationTask.execute(event, this);
      }
   }
}