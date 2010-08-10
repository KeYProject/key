// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.logic.op;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import de.uka.ilkd.key.logic.Term;

/** 
 * this class is used to represent the reference operator '.' 
 * in the shadow form (for transactions)
 */
public class ShadowAttributeOp extends AttributeOp implements ShadowedOperator {

    /** 
     * The pool of already created attribute operators. Ensures
     * 'singleton' property of attribute operators.
     */
    private static final WeakHashMap operatorPool = new WeakHashMap(50);
    
    /** 
     * returns and if neccessary creates the access operator of the
     * given attribute 
     * @return the attribute operator for the given attribute
     */
    public static ShadowAttributeOp 
           getShadowAttributeOp(IProgramVariable attribute) { 
	WeakReference attributeOpReference = 
	    (WeakReference) operatorPool.get(attribute);
	if (attributeOpReference == null || attributeOpReference.get() == null) {
	    // wrapping attributeOp in a weak reference is necessary as
	    // it contains a strong reference to its key
	    attributeOpReference = new WeakReference
		(new ShadowAttributeOp(attribute));
	    operatorPool.put(attribute, attributeOpReference);	    
	}
	return (ShadowAttributeOp)attributeOpReference.get();
    }

    /** 
     * creates a new shadow attribute operator.
     */
    private ShadowAttributeOp(IProgramVariable attribute) {
	super(attribute);
    }    

    /**
     * In contrast to the standard attribute access operator the arity
     * of a shadowed attribute is two. The first term denotes the object
     * whose field is accessed and second one stores a shadow marker.
     * @return arity of the Operator as int 
     */
    public int arity(){
        return 2;
    }

    /**
     * @return true if the operator is a shadowed 
     */
    public boolean isShadowed() {
	return true;
    }

    /**
     * returns the transaction number (shadow marker) of the given term
     * it assumes that the term's top operator is a ShadowedAttributeOp
     */
    public Term getTransactionNumber(Term t) {
	return t.sub(1);
    }

    /**
     * returns true if the given loc may be aliased by the current location 
     */
    public boolean mayBeAliasedBy(Location loc) {
        if (loc == this) {
            return true;
        }

        if (loc instanceof AttributeOp) {            
            return attributesAliased(((AttributeOp)loc).attribute());        
        }
        
        return false;
    }

    /**
     * @param variable
     * @return true if possibly aliased
     */
    private boolean attributesAliased(IProgramVariable variable) {
        boolean attributesAliased = 
            (variable instanceof SortedSchemaVariable ||
             attribute() instanceof SortedSchemaVariable);
        
        attributesAliased = attributesAliased ||
            variable == attribute();
        
        return attributesAliased;        
    }
    
    public String toString() {
        return ".(shadowed)"+attribute();
    }
} 
