// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit;


/**
 * this exception is raised when problems occurs
 * in the unit manager.
 */
public class UnitException extends Exception {

    public UnitException(String message) {
	super(message);
    }

    public UnitException(Exception e) {
	super(e);
    }

}
