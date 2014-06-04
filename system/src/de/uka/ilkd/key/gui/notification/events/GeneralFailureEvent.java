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
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * A notification event caused by a general unexpected failure
 * (usually caused by a bug of the system)
 * @author bubel
 */
public class GeneralFailureEvent extends NotificationEvent {

    private String errorMessage = "Unknown Error.";
    
    
    protected GeneralFailureEvent(int id) {
        super(id);
    }

    /**
     * creates an instance of this event
     * @param errorMessage a String describing the failure
     */
    public GeneralFailureEvent(String errorMessage) {
        super(NotificationEventID.GENERAL_FAILURE);
        this.errorMessage = errorMessage;
    }
    

    /**
     * @return the error message describing the reason for
     * this event    
     */
    public String getErrorMessage() {
        return errorMessage;
    }        
    
}