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


public class Intersect extends ADTPrefixConstruct {

    /**
     * 
     */
    private static final long serialVersionUID = 8777658515734186914L;


    public Intersect(Expression lhs, Expression rhs) {
	super(lhs, rhs);
	makeParentRoleValid();
    }


    protected Intersect(Intersect proto) {
	super(proto);
	makeParentRoleValid();
    }
    

    @Override    
    public Intersect deepClone() {
	return new Intersect(this);
    }


    @Override    
    public int getArity() {
	return 2;
    }

    
    @Override    
    public int getPrecedence() {
	return 0;
    }

    
    @Override    
    public int getNotation() {
	return PREFIX;
    }
}
