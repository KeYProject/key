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


public class MissingInstantiationException 
    extends SVInstantiationExceptionWithPosition {

    private String toInstantiate;
         
    public MissingInstantiationException( String toInstantiate, 
					  int    row, 
					  int    column,
					  boolean inIfSequent) {
	super("Missing Instantantiation", row, column, inIfSequent);
	this.toInstantiate = toInstantiate;
    }
        
    public String getMessage ()
    {
	String errmsg = super.getMessage();
	errmsg += "\n Instantiation missing for " + toInstantiate;
	return errmsg;
    }    

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return getMessage();
    }
}
