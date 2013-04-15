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
import recoder.list.generic.ASTArrayList;


public class SeqReverse extends ADTPrefixConstruct {

    /**
     * 
     */
    private static final long serialVersionUID = -4836079248155746383L;

    public SeqReverse(Expression e) {
	children = new ASTArrayList<Expression>(getArity());
	children.add(e);
	makeParentRoleValid();
    }


    protected SeqReverse(SeqReverse proto) {
	super(proto);
	makeParentRoleValid();
    }
    

    @Override    
    public SeqReverse deepClone() {
	return new SeqReverse(this);
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
        return "\\seq_reverse("+children.get(0).toSource()+")";
    }
}
