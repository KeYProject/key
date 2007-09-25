package de.uka.ilkd.key.unittest;

import java.util.HashSet;

import de.uka.ilkd.key.java.Expression;

public abstract class ValueContainer{

    protected HashSet values;

    public ValueContainer(Object v){
	values = new HashSet();
	add(v);
    }

    public ValueContainer(Object o1, Object o2){
	values = new HashSet();
	add(o1);
	add(o2);
    }

    public abstract Expression[] getValuesAsExpressions();

    public abstract ValueContainer union(ValueContainer v);

    public boolean equals(Object o){
	if(!(o instanceof ValueContainer)){
	    return false;
	}
	ValueContainer vc = (ValueContainer) o;
	return values.equals(vc.values);
    }

    public boolean contains(Object o){
	if(o instanceof ValueContainer){
	    return values.containsAll(((ValueContainer) o).values);
	}
	return values.contains(o);
    }

    public int hashCode(){
	return 7+13*values.hashCode();
    }

    private void add(Object o){
	if(o instanceof ValueContainer){
	    values.addAll(((ValueContainer) o).values);
	}else{
	    values.add(o);
	}
    }

    public String toString(){
	return "values: "+values;
    }


}
