// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

public class SVRigidnessException 
    extends SVInstantiationExceptionWithPosition {

    private String toInstantiate;
         
    public SVRigidnessException( String toInstantiate, 
				 int    row, 
				 int    column ) {
	super("Non-rigid term/formula", row, column, false);
	this.toInstantiate = toInstantiate;
    }
        
    public String getMessage ()
    {
	String errmsg = super.getMessage();
	errmsg += "\n " + toInstantiate +
	    " may be instantiated with rigid terms/formulas only";
	return errmsg;
    }    

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return getMessage();
    }
}
