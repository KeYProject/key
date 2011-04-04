// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;
import recoder.list.generic.ASTArrayList;


public class SeqSub extends Operator {

    public SeqSub(Expression e1, Expression e2, Expression e3) {
	children = new ASTArrayList<Expression>(getArity());
	children.add(e1);
	children.add(e2);
	children.add(e3);
	makeParentRoleValid();
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
    public int getPrecedence() {
	return 0;
    }

    
    @Override    
    public int getNotation() {
	return PREFIX;
    }
   
    
    @Override    
    public void accept(SourceVisitor v) {
	
    }
    
}
