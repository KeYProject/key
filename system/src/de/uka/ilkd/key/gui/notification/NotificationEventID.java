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

/**
 * This interface constants used to uniquely identify 
 * KeY system events
 * @author bubel
 */
public interface NotificationEventID {

    /** reserved for dummy implementations */
    int RESERVED = -1; // used by dummy implementation
    /** tasks notifying about proof closed events have this ID */
    int PROOF_CLOSED = 0;
    /** tasks notifying about abandoned tasks have this ID */
    int TASK_ABANDONED = 1;
    /** tasks notifying about general failures */
    int GENERAL_FAILURE = 2;    
    /** tasks notifying the user when KeY is shutdown have this ID */
    int EXIT_KEY = 3;
    /** tasks used to inform the user should have this ID */
    int GENERAL_INFORMATION = 4;
    
    /** tasks used to inform the user should have this ID */
    int EXCEPTION_CAUSED_FAILURE = 5;

    
    
}