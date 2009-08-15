// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import java.util.Iterator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;

public class BooleanValueContainer extends ValueContainer{

    public BooleanValueContainer(Boolean bool){
	super(bool);
    }

    public BooleanValueContainer(Object o1, Object o2){
	super(o1, o2);
    }

    public ValueContainer union(ValueContainer v){
	return new BooleanValueContainer(this, v);
    }

    public Expression[] getValuesAsExpressions(){
	Expression[] res = new Expression[values.size()];
	int i = 0;
	Iterator it = values.iterator();
	while(it.hasNext()){
	    res[i++] = ((Boolean) it.next()).booleanValue() ? 
		BooleanLiteral.TRUE : BooleanLiteral.FALSE;
	}
	return res;
    }

}
