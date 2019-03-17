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
 * This interface constants used to uniquely identify KeY system events
 * 
 * Refactored this type into an enum. // Kai Walisch 06/2015
 * 
 * @author bubel
 */
public enum NotificationEventID {

   /** tasks notifying about proof closed events have this ID */
   PROOF_CLOSED,
   /** tasks notifying about abandoned tasks have this ID */
   TASK_ABANDONED,
   /** tasks notifying about general failures */
   GENERAL_FAILURE,
   /** tasks notifying the user when KeY is shutdown have this ID */
   EXIT_KEY,
   /** tasks used to inform the user should have this ID */
   GENERAL_INFORMATION,
   /** tasks used to inform the user should have this ID */
   EXCEPTION_CAUSED_FAILURE

}