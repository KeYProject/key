// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;

public class IntValueContainer extends ValueContainer{

    public IntValueContainer(Integer i){
	super(i);
    }

    public IntValueContainer(Object o1, Object o2){
	super(o1, o2);
    }

    public ValueContainer union(ValueContainer v){
	return new IntValueContainer(this, v);
    }

    public Expression[] getValuesAsExpressions(){
	Expression[] res = new Expression[values.size()];
	int i = 0;
        for (Object value : values) {
            res[i++] = new IntLiteral(((Integer) value).intValue());
        }
	return res;
    }
}
