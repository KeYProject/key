// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden  
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.asmkey.proof.init;

/**
 * This exception is raised when someone tries
 * to set new services to the asmkey InitConfig
 *
 * @author Stanislas Nanchen
 * @see InitConfig
 */
public class InitConfigException extends RuntimeException {
    
    public InitConfigException(String m) {
	super(m);
    }
}
