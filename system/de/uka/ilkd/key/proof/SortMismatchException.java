// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.logic.sort.Sort;


public class SortMismatchException 
    extends SVInstantiationExceptionWithPosition {

    private String toInstantiate;
    private Sort   givenSort;
         
    public SortMismatchException( String toInstantiate,
				  Sort   givenSort,
				  int    row, 
				  int    column ) {
	super("Sorts mismatch", row, column, false);
	this.toInstantiate = toInstantiate;
	this.givenSort     = givenSort;
    }
        
    public String getMessage ()
    {
	String errmsg = super.getMessage();
	errmsg += "\n Sort of instantiation given for " + toInstantiate + ", " + givenSort +
	    ", is illegal at this place.";
	return errmsg;
    }    

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return getMessage();
    }
}
