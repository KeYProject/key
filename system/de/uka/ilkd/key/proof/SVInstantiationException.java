// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;


public abstract class SVInstantiationException extends Exception {

    private String description;        
         
    public SVInstantiationException ( String description ) {
	super("Instantiation Error");
	this.description = description;
    }

    public String getMessage () {
	return description;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return getMessage();
    }
}
