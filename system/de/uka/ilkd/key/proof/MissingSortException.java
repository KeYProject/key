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


public class MissingSortException 
    extends SVInstantiationExceptionWithPosition {

    private String toInstantiate;
         
    public MissingSortException( String toInstantiate, 
				 int    row, 
				 int    column ) {
	super("Missing Sort", row, column, false);
	this.toInstantiate = toInstantiate;
    }
        
    public String getMessage ()
    {
	String errmsg = super.getMessage();
	errmsg += "\n Sort of " + toInstantiate + " is unknown.\n" +
	    "The sort can be given manually using an expression like \"id:sort\".";
	return errmsg;
    }    

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return getMessage();
    }
}
