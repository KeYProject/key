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


public class SeqSingleton extends ADTPrefixConstruct {

    /**
     * 
     */
    private static final long serialVersionUID = 940102046205262465L;

    public SeqSingleton(Expression lhs) {
	super(lhs);
	makeParentRoleValid();
    }


    protected SeqSingleton(SeqSingleton proto) {
	super(proto);
	makeParentRoleValid();
    }
    

    @Override    
    public SeqSingleton deepClone() {
	return new SeqSingleton(this);
    }


    @Override    
    public int getArity() {
	return 1;
    }

    
    @Override    
    public int getNotation() {
	return PREFIX;
    }
    
    @Override
    public String toSource(){
        return "\\seq_singleton("+children.get(0)+")";
    }
}