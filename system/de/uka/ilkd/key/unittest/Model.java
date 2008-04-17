// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import java.util.*;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.expression.literal.*;

/**
 * Contains a mapping of locations to concrete values for them.
 */
public class Model{

    protected static final Boolean boolTrue = new Boolean(true);
    protected static final Boolean boolFalse = new Boolean(false);

    private HashMap class2value;
    private HashMap term2class;

    public Model(HashMap term2class){
	this(new HashMap(), term2class);
    }

    private Model(HashMap class2value, HashMap term2class){
	this.class2value = class2value;
	this.term2class = term2class;
    }

    public Model copy(){
	return new Model((HashMap) class2value.clone(), term2class);
    }

    public void setValue(EquivalenceClass ec){
	if(ec.isInt()){
	    class2value.put(ec, new IntValueContainer(
				ec.getConcreteIntValue(term2class)));
	}else if(ec.isBoolean()){
	    class2value.put(ec, new BooleanValueContainer(
				ec.getConcreteBooleanValue(term2class)));
	}
    }

    public void setValue(EquivalenceClass ec, int i){
	class2value.put(ec, new IntValueContainer(new Integer(i)));
    }

    public void setValue(EquivalenceClass ec, boolean b){
	class2value.put(ec, b ? 
			new BooleanValueContainer(boolTrue) : 
			new BooleanValueContainer(boolFalse));
    }

    public void setValue(EquivalenceClass ec, ValueContainer vc){
	class2value.put(ec, vc);
    }

    public int size(){
	return class2value.size();
    }

    /**
     * Returns an array of possible values <code>ec</code> can have in this 
     * model.
     */
    // currently merging of models is disabled, so <code>ec</code> has always
    // only one value
    public Expression[] getValuesAsExpressions(EquivalenceClass ec){
	Object o = class2value.get(ec);
/*	if(o instanceof Integer){
	    return new Expression[]{new IntLiteral(((Integer) o).intValue())};
	}
	if(o instanceof Boolean){
	    return new Expression[]{(o==boolTrue ? 
				     BooleanLiteral.TRUE : 
				     BooleanLiteral.FALSE)};
				     }*/
	if(o == null){
	    return new Expression[]{new IntLiteral(15)};
	}
	if(o instanceof ValueContainer){
	    return ((ValueContainer) o).getValuesAsExpressions();
	}
	return null;
    }

    /**
     * Returns the value <code>ec</code> has in this model.
     */
    public Expression getValueAsExpression(EquivalenceClass ec){
	Expression[] earr = getValuesAsExpressions(ec);
	if(earr!=null){
	    return earr[0];
	}
	return null;
    }

    public ValueContainer getValue(EquivalenceClass ec){
	return (ValueContainer) class2value.get(ec);
    }

    /** If m differs from this model only by one value the models are merged,
     * i.e. the one differing entry is replaced by an interval created from
     * the two different values of the corresponding equivalence class.
     * Iff the merge is successful or this Model already subsumes m
     * true is returned.
     */
    public boolean merge(Model m){
	EquivalenceClass diff = null;
	Iterator it = class2value.keySet().iterator();
	ValueContainer newValue = null;
	boolean superSet = true;
	int neCount = 0;
	while(it.hasNext()){
	    EquivalenceClass ec = (EquivalenceClass) it.next();
	    ValueContainer v0 = getValue(ec);
	    ValueContainer v1 = m.getValue(ec);
	    if(!v0.equals(v1)){
		neCount++;
		if(diff == null){
		    if(neCount > 1){
			return false;
		    }
		    if(!v0.contains(v1)){
			diff = ec;
			newValue = v0.union(v1);
		    }
		}else if(neCount > 1){
		    return false;
		}
	    }
	    if(!v0.contains(v1)){
		superSet = false;
	    }
	}
	if(diff != null && newValue != null){
	    class2value.put(diff, newValue);
	    return true;
	}else{
	    return superSet;
	}
    }

    public int hashCode(){
	return 17;
    }

    public String toString(){
	String result = "Model :\n{\n";
	Iterator it = class2value.keySet().iterator();
	while(it.hasNext()){
	    Object o = it.next();	    
	    result += o+" = "+class2value.get(o)+"\n";
	}
	result += "}";
	return result;
    }

    public boolean equals(Object o){
	if(o==null || !(o instanceof Model)){
	    return false;
	}
	return class2value.equals(((Model) o).class2value);
    }
}
