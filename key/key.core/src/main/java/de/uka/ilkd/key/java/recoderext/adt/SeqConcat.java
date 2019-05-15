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

package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;


public class SeqConcat extends ADTPrefixConstruct {

    /**
     * 
     */
    private static final long serialVersionUID = -5950638934821692317L;

    public SeqConcat(Expression lhs, Expression rhs) {
	super(lhs, rhs);
	makeParentRoleValid();
    }


    protected SeqConcat(SeqConcat proto) {
	super(proto);
	makeParentRoleValid();
    }
    

    @Override    
    public SeqConcat deepClone() {
	return new SeqConcat(this);
    }


    @Override    
    public int getArity() {
	return 2;
    }

    
    @Override    
    public int getNotation() {
	return PREFIX;
    }
    
    @Override
    public String toSource(){
        return "\\seq_concat("+children.get(0).toSource()+","+children.get(1).toSource()+")";
    }
}