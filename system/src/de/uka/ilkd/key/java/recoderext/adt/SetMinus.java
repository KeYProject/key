// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;


public class SetMinus extends ADTPrefixConstruct {

    public SetMinus(Expression lhs, Expression rhs) {
	super(lhs, rhs);
	makeParentRoleValid();
    }


    protected SetMinus(SetMinus proto) {
	super(proto);
	makeParentRoleValid();
    }
    

    @Override    
    public SetMinus deepClone() {
	return new SetMinus(this);
    }


    @Override    
    public int getArity() {
	return 2;
    }

    
    @Override    
    public int getNotation() {
	return PREFIX;
    }
}
