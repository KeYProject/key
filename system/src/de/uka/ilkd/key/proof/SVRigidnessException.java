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

public class SVRigidnessException 
    extends SVInstantiationExceptionWithPosition {

    /**
     * 
     */
    private static final long serialVersionUID = -440942650851579438L;
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
