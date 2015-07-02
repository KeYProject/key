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

import javax.swing.JFrame;

import de.uka.ilkd.key.gui.notification.actions.GeneralFailureJTextPaneDisplay;

/**
 * This task notifies the user about an unexpected error.
 * @author bubel
 */
public class GeneralFailureNotification extends NotificationTask {

    public GeneralFailureNotification(JFrame comp) {
       addNotificationAction(new GeneralFailureJTextPaneDisplay(comp));
   }

   /**
     * returns if this task should be executed in auto mode
     * @return if true execute task even if in automode
     */
    @Override
   protected boolean automodeEnabledTask() {   
        return true;
    }

    /** 
     * @return the event id of a general failure event
     * @see NotificationEventID
     */
    @Override
   public NotificationEventID getEventID() {
        return NotificationEventID.GENERAL_FAILURE;
    }

}