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
 * Created on 30.03.2005
 */
package de.uka.ilkd.key.gui.notification;

import de.uka.ilkd.key.gui.notification.events.NotificationEvent;

/**
 * This notification task is used to inform the user about a non-error
 * situation (e.g. statistics (how many goals have been closed) etc.) 
 * @author bubel
 */
public class GeneralInformationNotification extends NotificationTask {

     
    /**
     * @see NotificationTask#executeImpl(NotificationEvent, NotificationManager)      
     */
    protected void executeImpl(NotificationEvent event,
            NotificationManager manager) {
        for (final NotificationAction action : getNotificationActions()) {         
            action.execute(event);
        }
    }

    /** 
     * @return the event id of a general information event
     * @see NotificationEventID
     */
    public int getEventID() {
        return NotificationEventID.GENERAL_INFORMATION;
    }

}
