// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;

/**
 * Shadow Array access operator used in transactions
 */
public class ShadowArrayOp extends ArrayOp implements ShadowedOperator {

    /** 
     * The pool of already created array operators. Ensures
     * 'singleton' property of array operators.
     */
    private static final WeakHashMap operatorPool = new WeakHashMap(50);
    
    /**
     * returns and if neccessary creates the array access operator for the given
     * array sort
     * 
     * @param arraySort
     *            the ArraySort to which this operator is applicable
     * @return the array access operator for the given array sort
     */
    public static ShadowArrayOp getShadowArrayOp(Sort arraySort) {
        Debug.assertTrue(arraySort instanceof ArraySort ||
                         arraySort instanceof ProgramSVSort || 
                         arraySort instanceof GenericSort ||
                         arraySort == AbstractMetaOperator.METASORT,
                         arraySort + " is no allowed array sort.");
        WeakReference arrayAccessOpReference = (WeakReference) operatorPool
                .get(arraySort);
        if (arrayAccessOpReference == null
                || arrayAccessOpReference.get() == null) {
            // wrapping attributeOp in a weak reference is necessary as
            // it contains a strong reference to its key
            arrayAccessOpReference = 
                   new WeakReference(new ShadowArrayOp(arraySort));
            operatorPool.put(arraySort, arrayAccessOpReference);
        }
        return (ShadowArrayOp)arrayAccessOpReference.get();
    } 
    
    
    /**
     * creates an ShadowArrayOp
     */
    ShadowArrayOp(Sort arraySort){
        super(new Name("shadowed-access(" + arraySort +")"), arraySort);
    }
    
    /** @return arity of the Operator as int */
    public int arity(){
        return 3;
    }

    /**
     * @return true if the operator is a shadowed 
     */
    public boolean isShadowed() {
	return true;
    }

    public Term getTransactionNumber(Term t) {
	return t.sub(2);
    }

    public boolean mayBeAliasedBy(Location loc) {
        if (loc == this) return true;
        
        if (loc instanceof ArrayOp) {
            ArrayOp locAsArray = (ArrayOp) loc;
            if ((locAsArray.sort instanceof ProgramSVSort ||
                 sort instanceof ProgramSVSort || 
                 sort == AbstractMetaOperator.METASORT) ||
                 arraySortAliased(locAsArray.arraySort(), arraySort())) {
               return true;
            }           
        }
        return false;
    }
    
    public String toString() {
        return "[](shadowed, "+arraySort()+")";
    }
}

