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
 * Created on 30.03.2005
 */
package de.uka.ilkd.key.gui.notification.events;

import de.uka.ilkd.key.gui.notification.NotificationEventID;

/**
 * If the system wants to inform the user it may emit this event. If the 
 * flavour of the information is that of an error message, one should use the 
 * {@link de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent}
 * instead.
 */
public class GeneralInformationEvent extends NotificationEvent {

   /** the message with the information to be displayed */
    private final String informationMessage;
    
    /** the context/ category of this message (e.g. used as window title) */
    private final String context;
        
    /**
     * Creates an event informing the user about the fact given as string
     * @param context the String describing the context/category of the 
     * information (e.g. used as window title, head line etc.)
     * @param informationMessage the String containing the information
     */
    public GeneralInformationEvent(String context, String informationMessage) {
        super(NotificationEventID.GENERAL_INFORMATION);
        this.context = context;
        this.informationMessage = informationMessage;        
    }
    
    /**
     * Creates an event informing the user about the fact given as string
     * @param informationMessage the String containing the information  
     */
    public GeneralInformationEvent(String informationMessage) {
        this("Information", informationMessage);              
    }

    /**
     * returns the context as string      
     */
    public String getContext() {
        return context;
    }
    
    /**
     * returns the information as string      
     */
    public String getMessage() {
        return informationMessage;
    }
    
    
}