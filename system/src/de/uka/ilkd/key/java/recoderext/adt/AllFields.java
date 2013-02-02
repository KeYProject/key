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


package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;


public class AllFields extends ADTPrefixConstruct {

    /**
     * 
     */
    private static final long serialVersionUID = 3940415948467563540L;


    public AllFields(Expression lhs) {
	super(lhs);
	makeParentRoleValid();
    }


    protected AllFields(AllFields proto) {
	super(proto);
	makeParentRoleValid();
    }
    

    @Override    
    public AllFields deepClone() {
	return new AllFields(this);
    }


    @Override    
    public int getArity() {
	return 1;
    }

    
    @Override    
    public int getNotation() {
	return PREFIX;
    }
   
}
