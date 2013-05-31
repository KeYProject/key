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

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * The proof closed notification notifies the user about a successful attempt 
 * closing a proof. 
 * @author bubel
 */
public class ProofClosedNotification extends NotificationTask {

    
    /**
     * Creates a proof closed notification task.     
     */
    public ProofClosedNotification() {       
    }

    /**
     * returns if this task should be executed in auto mode
     * @return if true execute task even if in automode
     */
    protected boolean automodeEnabledTask() {   
        return true;
    }
    
    /**
     * @return the event if of this task
     */
    public int getEventID() {       
        return NotificationEventID.PROOF_CLOSED;
    }     
    
    /**
     * executes the proof closed notification task
     */
    public void executeImpl (NotificationEvent event, NotificationManager manager) {
        for (final NotificationAction action : getNotificationActions()) {         
            action.execute(event);
        }
   }
}
