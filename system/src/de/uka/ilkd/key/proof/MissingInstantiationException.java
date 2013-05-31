// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof;


public class MissingInstantiationException 
    extends SVInstantiationExceptionWithPosition {

    /**
     * 
     */
    private static final long serialVersionUID = 6424217152885699595L;
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
