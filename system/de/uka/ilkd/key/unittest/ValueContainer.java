// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import java.util.HashSet;

import de.uka.ilkd.key.java.Expression;

public abstract class ValueContainer{

    protected HashSet<Object> values;

    public ValueContainer(Object v){
	values = new HashSet<Object>();
	add(v);
    }

    public ValueContainer(Object o1, Object o2){
	values = new HashSet<Object>();
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
