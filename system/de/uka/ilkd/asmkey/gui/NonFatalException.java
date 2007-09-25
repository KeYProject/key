// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.gui;

/**
 * This exception is raised when a grave but non fatal
 * exception is raised.
 * The two messages are:
 * 1. a short line explaining the problem;
 * 2. a longer message.
 */
public class NonFatalException extends Exception {

    String longMessage;
    
    public NonFatalException(String message, String longMessage) {
	super(message); 
	this.longMessage = longMessage;
    }
    
    public String getLongMessage() {
	return longMessage;
    }
}
