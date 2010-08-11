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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.GenericSortInstantiations;
import de.uka.ilkd.key.rule.inst.SortException;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

public class ArrayOp extends AccessOp implements SortDependingSymbol {

    /** 
     * The pool of already created array operators. Ensures
     * 'singleton' property of array operators.
     */
    private static final WeakHashMap operatorPool = new WeakHashMap(50);
    
    /** Sort of the array this operator addresses */
    protected final Sort sort;

    private final Sort dependingOnSort;

    private static final Name kind = new Name("arrayaccess");

    /**
     * returns and if neccessary creates the shadowed array access operator for 
     * the given array sort
     * 
     * @param arraySort the Sort to which this operator is applicable
     *  must be of kind {@link ArraySort} or {@link ProgramSVSort}
     * @return the array access operator for the given array sort
     */
    public static ArrayOp getArrayOp(Sort arraySort) {
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
                   new WeakReference(new ArrayOp(arraySort));
            operatorPool.put(arraySort, arrayAccessOpReference);
        }
        return (ArrayOp) arrayAccessOpReference.get();
    } 
    
    protected ArrayOp(Name name, Sort arraySort) {
        super(name);
        this.sort = arraySort;
        if (arraySort instanceof ProgramSVSort ||
                arraySort == AbstractMetaOperator.METASORT) {
            this.dependingOnSort = null;
        } else {
            this.dependingOnSort = arraySort;
        }
    }
    
    /**
     * creates an ArrayOp
     */
    private ArrayOp(Sort arraySort){
     this(new Name("arrayAccess_" 
                   + (arraySort instanceof ArraySort
                      ? ((ArraySort)arraySort).elementSort().toString() 
                      : arraySort.toString())), 
          arraySort);
    }
    
    /**
     * determines the sort of the {@link Term} if it would be created using this
     * Operator as top level operator and the given terms as sub terms. The
     * assumption that the constructed term would be allowed is not checked.
     * @param term an array of Term containing the subterms of a (potential)
     * term with this operator as top level operator
     * @return sort of the term with this operator as top level operator of the
     * given substerms
     */
    public Sort sort(Term[] term) {	
        if (sort instanceof ProgramSVSort || 
                sort instanceof GenericSort || 
                sort == AbstractMetaOperator.METASORT){ 
            return ProgramSVSort.NONSIMPLEEXPRESSION;
	}  
        return ((ArraySort)sort).elementSort();
    }
    
    /** checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.
     * @return true iff the top level structure of
     * the @link Term is valid.
     */
    public boolean validTopLevel(Term term) {
        Sort s = term.sub(0).sort();
        if ( sort instanceof ArraySort
             && ( s instanceof ArraySort || s == Sort.NULL ) ) {
            // missing check if term.sub(1) has integer sort
            return s.extendsTrans(sort); 
        } else if (sort instanceof ProgramSVSort || 
                sort instanceof GenericSort  || 
                sort == AbstractMetaOperator.METASORT) {
	    return true;
	}
	return false;	
    }

    /** 
     * the arity of an array access operator is <code>2</code> where the
     * first sub term denotes the array object itself and the second one
     * the accessed index
     * @return arity of the Operator as int 
     */
    public int arity(){
        return 2;
    }

    /**
     * @return true if the operator is a shadowed 
     */
    public boolean isShadowed() {
	return false;
    }
    
    /**
     * @return the array sort on which this operator is applied
     */
    public Sort arraySort() {
        return sort;
    }
    
    /**
     * @return the sort of this operator
     */
    public Sort sort() {
        return ((ArraySort)sort).elementSort();
    }
    
    /**
     * the top level operator of t must be <tt>this</tt>
     * returns the reference prefix of this array access for the given term
     */
    public Term referencePrefix(Term t) {
        Debug.assertTrue(t.op() == this);
        return t.sub(0);
    }
    
    /**
     * the top level operator of t must be <tt>this</tt>
     * returns the index of this array access for the given term
     */
    public Term index(Term t) {
        Debug.assertTrue(t.op() == this);
        return t.sub(1);
    }
    
    public de.uka.ilkd.key.java.Expression convertToProgram(Term t, 
							    ExtList el) {
	ReferencePrefix accessPath = (ReferencePrefix) el.get(0);
	el.remove(accessPath);
	return new ArrayReference(el, accessPath);
    }

    /**
     * tests if the location <code>loc</code> may be an alias of this array 
     * location
     * @param loc the Location to check
     * @return true iff <code>loc</code> may be an alias of the current (this) 
     *  location
     * @see de.uka.ilkd.key.logic.op.Location#mayBeAliasedBy
     *                      (de.uka.ilkd.key.logic.op.Location)
     */
    public boolean mayBeAliasedBy(Location loc) {        
        if ( !( loc instanceof ArrayOp )
             || ( loc instanceof ShadowedOperator ) )
            return false; 
        
        final ArrayOp aOp = (ArrayOp)loc;
        return arraySortAliased ( aOp.arraySort (), arraySort () )
	    || sort instanceof ProgramSVSort
	    || aOp.sort instanceof ProgramSVSort;
    }
    
    protected boolean arraySortAliased(Sort as1, Sort as2) {
        assert as1 instanceof ArraySort && as2 instanceof ArraySort;       
        return true;
    }
    
    /** 
     * implements the default operator matching rule which means 
     * that the compared object have to be equal otherwise
     * matching fails
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {                  
        if (subst.getClass() == this.getClass()) {
            if (getSortDependingOn() instanceof ProgramSVSort) {
                return mc;
            } else if (getSortDependingOn() instanceof GenericSort) {
                final GenericSortInstantiations genSortInst = 
                    mc.getInstantiations().getGenericSortInstantiations();
                final GenericSort gs = (GenericSort)getSortDependingOn();
                if (genSortInst.isInstantiated(gs)) {
                    final Sort s =  genSortInst.getRealSort(getSortDependingOn(), services);
                    assert s instanceof ArraySort;
                    return getArrayOp(s).match(subst, mc, services);
                } else {                  
                    final GenericSortCondition c = 
                        GenericSortCondition.createIdentityCondition(
                                gs, 
                                ((ArrayOp)subst).getSortDependingOn());                                               
                    if ( c == null ) {
                        Debug.out("FAILED. Generic sort condition");
                        return null; //FAILED;
                    } else {
                        try {                   
                            mc = mc
                            .setInstantiations ( mc.getInstantiations ().
                                    add ( c ) );
                        } catch ( SortException e ) {
                            Debug.out("FAILED. Sort mismatch.", gs, 
                                    ((ArrayOp)subst).getSortDependingOn() );
                            return null; //FAILED;
                        }
                    }                                      
                    return mc;
                }
            } else if (getSortDependingOn() == null) {
                // array operators occuring in find expressions must be 
                // qualified
                assert false;
            }
        }
        return super.match(subst, mc, services);

    }

    public String toString() {
        return "[]("+arraySort()+")";
    }

    public SortDependingSymbol getInstanceFor(SortDefiningSymbols p_sort) {                
        return getArrayOp(p_sort);
    }

    public Name getKind() {        
        return kind;
    }

    public Sort getSortDependingOn() {     
        return dependingOnSort;
    }

    public boolean isSimilar(SortDependingSymbol p) {        
        
        return p!=null && p.getKind().equals(this.getKind());
    }

   
}

