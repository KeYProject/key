package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.*;

import java.util.*;

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
	Iterator it = values.iterator();
	while(it.hasNext()){
	    res[i++] = new IntLiteral(((Integer) it.next()).intValue());
	}
	return res;
    }
}
