// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.recoderext.ldt;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;


public class Singleton extends Operator {

    public Singleton(Expression lhs) {
	super(lhs);
	makeParentRoleValid();
    }


    protected Singleton(Singleton proto) {
	super(proto);
	makeParentRoleValid();
    }
    

    @Override    
    public Singleton deepClone() {
	return new Singleton(this);
    }


    @Override    
    public int getArity() {
	return 1;
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
