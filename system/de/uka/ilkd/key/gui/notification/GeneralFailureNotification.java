// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on 18.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import java.util.Iterator;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * This task notifies the user about an unexpected error.
 * @author bubel
 */
public class GeneralFailureNotification extends NotificationTask {

    /**
     * returns if this task should be executed in auto mode
     * @return if true execute task even if in automode
     */
    protected boolean automodeEnabledTask() {   
        return true;
    }
    
    /**
     * @see NotificationTask#executeImpl(NotificationEvent, NotificationManager)
     */
    protected void executeImpl(NotificationEvent event,
            NotificationManager manager) {
        final Iterator actions = getActions();         
        while (actions.hasNext()) {            
            ((NotificationAction)actions.next()).execute(event);
        }
    }

    /** 
     * @return the event id of a general failure event
     * @see NotificationEventID
     */
    public int getEventID() {
        return NotificationEventID.GENERAL_FAILURE;
    }

}
