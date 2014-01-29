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


public class SeqSub extends ADTPrefixConstruct {

    /**
     * 
     */
    private static final long serialVersionUID = 9034359926577584988L;

    public SeqSub(Expression e1, Expression e2, Expression e3) {
	children = new ASTArrayList<Expression>(getArity());
	children.add(e1);
	children.add(e2);
	children.add(e3);
	makeParentRoleValid();
    }
    
    public SeqSub(ADTPrefixConstruct seq, RangeExpression range){
        this(seq, (Expression) range.getChildAt(0), (Expression) range.getChildAt(1));
    }


    protected SeqSub(SeqSub proto) {
	super(proto);
	makeParentRoleValid();
    }
    

    @Override    
    public SeqSub deepClone() {
	return new SeqSub(this);
    }


    @Override    
    public int getArity() {
	return 3;
    }

    
    @Override    
    public int getNotation() {
	return PREFIX;
    }
    
    @Override
    public String toSource(){
        return children.get(0).toSource()+"["+children.get(1)+".."+children.get(2)+"]";
    }

    
}
