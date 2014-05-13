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
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * A NotificationEvent is triggered if the system wants to notify the user
 * about a certain situation. Each kind of event is assigned a unique id
 * which are declared in {@link de.uka.ilkd.key.gui.notification.NotificationEventID}.
 * @author bubel
 */
public abstract class NotificationEvent {

    /** the unique id identifying the kind of this event */
    private final int eventID;
           
    /**
     * creates an instance of this event
     * @param eventID the int identifying the kind of this event
     * @see NotificationEventID
     */
    public NotificationEvent(int eventID) {
        this.eventID = eventID;        
    }

    /**
     * @return returns the eventID
     * @see NotificationEventID    
     */
    public int getEventID() {
        return eventID;
    }
        
}