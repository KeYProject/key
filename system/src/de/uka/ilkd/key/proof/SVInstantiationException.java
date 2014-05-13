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

package de.uka.ilkd.key.proof;


public abstract class SVInstantiationException extends Exception {

    /**
     * 
     */
    private static final long serialVersionUID = 7716370813981234134L;
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