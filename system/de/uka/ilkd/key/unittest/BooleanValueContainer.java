package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.*;

import java.util.*;

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
