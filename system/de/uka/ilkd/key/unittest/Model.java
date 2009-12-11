// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Term;

/**
 * Contains a mapping of locations to concrete values for them.
 */
public class Model {

    protected static final Boolean boolTrue = new Boolean(true);

    protected static final Boolean boolFalse = new Boolean(false);

    private HashMap<EquivalenceClass, ValueContainer> class2value;

    private HashMap<Term, EquivalenceClass> term2class;

    public Model(HashMap<Term, EquivalenceClass> term2class) {
	this(new HashMap<EquivalenceClass, ValueContainer>(), term2class);
    }

    private Model(HashMap<EquivalenceClass, ValueContainer> class2value,
	    HashMap<Term, EquivalenceClass> term2class) {
	this.class2value = class2value;
	this.term2class = term2class;
    }

    public Model copy() {
	return new Model((HashMap) class2value.clone(), term2class);
    }

    public void setValue(EquivalenceClass ec) {
	if (ec.isInt()) {
	    class2value.put(ec, new IntValueContainer(ec
		    .getConcreteIntValue(term2class)));
	} else if (ec.isBoolean()) {
	    class2value.put(ec, new BooleanValueContainer(ec
		    .getConcreteBooleanValue(term2class)));
	}
    }

    /**Warning: this method does not set a value to the EquivalenceClass given as argument
     * but instead an association is made between the equivalence class and the value.
     * This Association is stored in a hashmap of this class and not of the equivalence class */
    public void setValue(EquivalenceClass ec, int i) {
	class2value.put(ec, new IntValueContainer(new Integer(i)));
    }

    public void setValue(EquivalenceClass ec, boolean b) {
	class2value.put(ec, b ? new BooleanValueContainer(boolTrue)
		: new BooleanValueContainer(boolFalse));
    }

    // public void setValue(EquivalenceClass ec, ValueContainer vc) {
    // class2value.put(ec, vc);
    // }

    public int size() {
	return class2value.size();
    }

    /**
     * Returns an array of possible values <code>ec</code> can have in this
     * model.
     */
    // currently merging of models is disabled, so <code>ec</code> has always
    // only one value
    public Expression[] getValuesAsExpressions(EquivalenceClass ec) {
	Object o = class2value.get(ec);
	/*
	 * if(o instanceof Integer){ return new Expression[]{new
	 * IntLiteral(((Integer) o).intValue())}; } if(o instanceof Boolean){
	 * return new Expression[]{(o==boolTrue ? BooleanLiteral.TRUE :
	 * BooleanLiteral.FALSE)}; }
	 */
	/*
	if (o == null) {
	    return new Expression[] { new IntLiteral(15) };
	}
	*/
	if (o instanceof ValueContainer) {
	    return ((ValueContainer) o).getValuesAsExpressions();
	}
	return null;
    }

    /**
     * Returns the value <code>ec</code> has in this model.
     */
    public Expression getValueAsExpression(EquivalenceClass ec) {
	Expression[] earr = getValuesAsExpressions(ec);
	if (earr != null) {
	    return earr[0];
	}
	return null;
    }

    // private ValueContainer getValue(EquivalenceClass ec) {
    // return class2value.get(ec);
    // }

    // /**
    // * If m differs from this model only by one value the models are merged,
    // * i.e. the one differing entry is replaced by an interval created from
    // the
    // * two different values of the corresponding equivalence class. Iff the
    // * merge is successful or this Model already subsumes m true is returned.
    // */
    // public boolean merge(Model m) {
    // EquivalenceClass diff = null;
    // Iterator<EquivalenceClass> it = class2value.keySet().iterator();
    // ValueContainer newValue = null;
    // boolean superSet = true;
    // int neCount = 0;
    // while (it.hasNext()) {
    // EquivalenceClass ec = it.next();
    // ValueContainer v0 = getValue(ec);
    // ValueContainer v1 = m.getValue(ec);
    // if (!v0.equals(v1)) {
    // neCount++;
    // if (diff == null) {
    // if (neCount > 1) {
    // return false;
    // }
    // if (!v0.contains(v1)) {
    // diff = ec;
    // newValue = v0.union(v1);
    // }
    // } else if (neCount > 1) {
    // return false;
    // }
    // }
    // if (!v0.contains(v1)) {
    // superSet = false;
    // }
    // }
    // if (diff != null && newValue != null) {
    // class2value.put(diff, newValue);
    // return true;
    // } else {
    // return superSet;
    // }
    // }

    public int hashCode() {
	return 17;
    }

    public String toString() {
	String result = "Model :\n{\n";
        for (EquivalenceClass equivalenceClass : class2value.keySet()) {
            Object o = equivalenceClass;
            result += o + " = " + class2value.get(o) + "\n";
        }
	result += "}";
	return result;
    }

    public boolean equals(Object o) {
	if (o == null || !(o instanceof Model)) {
	    return false;
	}
	return class2value.equals(((Model) o).class2value);
    }
}
