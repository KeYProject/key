// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.IntersectionSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.SortException;
import de.uka.ilkd.key.util.Debug;

/**
 * A sort depending function is a function symbol. 
 * The following invariant has to hold:<br>
 *   given two sort depending functions f1 and f2 then</br> 
 *     from f1.isSimilar(f2) and f1.getSortDependingOn() == f2.getSortDependingOn() <br/>
 *     follows f1 == f2 
 */
public class SortDependingFunction extends RigidFunction
    implements SortDependingSymbol {
    
    private final Name kind;
    private final Sort sortDependingOn;

    /** creates a Function 
     * @param name String with name of the function
     * @param sort the Sort of the function (result type)
     * @param kind name of the kind this object belongs to
     * @param sortDependingOn sort this object is depending on, this
     * is the difference between various objects of the same kind
     */   
    public SortDependingFunction ( Name   name,
				   Sort   sort,
				   Sort[] argSorts,
				   Name   kind,
				   Sort   sortDependingOn ) {
	super ( name, sort, argSorts );
	this.kind            = kind;
	this.sortDependingOn = sortDependingOn;
    }

    public SortDependingFunction ( Name        name,
				   Sort        sort,
				   ImmutableArray<Sort> argSorts,
				   Name        kind,
				   Sort        sortDependingOn ) {
	super ( name, sort, argSorts );
	this.kind            = kind;
	this.sortDependingOn = sortDependingOn;
    }

    /**
     * @return the sort this object has been instantiated for
     */
    public Sort    getSortDependingOn () {
	return sortDependingOn;
    }

    /**
     * Compares "this" and "p"
     * @param p object to compare
     * @return true iff this and p are instances of the same kind of
     * symbol, but possibly instantiated for different sorts
     */
    public boolean isSimilar          ( SortDependingSymbol p ) {
	return getKind ().equals ( p.getKind () );
    }

    /**
     * Assign a name to this term symbol, independant of concrete
     * instantiations for different sorts
     * @return the kind of term symbol this object is an instantiation
     * for
     */
    public Name    getKind            () {
	return kind;
    }

    /**
     * Get the instance of this term symbol defined by the given sort
     * "p_sort"
     * @return a term symbol similar to this one, or null if this
     * symbol is not defined by "p_sort"
     *
     * POSTCONDITION: result==null || (this.isSimilar(result) &&
     * result.getSortDependingOn()==p_sort)
     */
    public SortDependingSymbol getInstanceFor ( SortDefiningSymbols p_sort ) {
	return p_sort.lookupSymbol ( getKind () );
    }

    
    /**
     * tries to match sort <code>s1</code> to fit sort <code>s2</code>
     * @param s1 Sort tried to matched (maybe concrete or (contain) generic)
     * @param s2 concrete Sort 
     * @param mc the MatchConditions up to now
     * @return <code>null</code> if failed the resulting match conditions otherwise 
     */
    private MatchConditions matchSorts(Sort s1, Sort s2, MatchConditions mc) {                
        Debug.assertFalse(s2 instanceof GenericSort,
                         "Internal Error. Sort s2 is not allowed to be of type generic.");
        if (!(s1 instanceof GenericSort)) {
            if (s1.getClass() != s2.getClass()) {
                Debug.out("Not unifiable sorts.", s1, s2);
                return null;
            }
            if (s1 instanceof IntersectionSort) {
                final IntersectionSort intersect1 = (IntersectionSort)s1;                
                final IntersectionSort intersect2 = (IntersectionSort)s2;

                if (intersect1.memberCount() != intersect2.memberCount()) {
                    Debug.out("Should not happen as intersection sorts should always "+ 
                              "have member count = 2");
                    return null;
                }                
                for (int i = 0, sz = intersect1.memberCount(); i<sz; i++) {
                    mc = matchSorts(intersect1.getComponent(i), 
                                    intersect2.getComponent(i), mc);
                    if (mc == null) {
                        Debug.out("Failed matching ", intersect1, intersect2);
                        return null;
                    }
                }
            } if (s1 == s2) {
                return mc;
            } else {
                Debug.out("FAIL. Sorts not identical.", s1, s2);
                return null;
            }
        } else {        
            final GenericSort gs = (GenericSort)s1;
            final GenericSortCondition c = 
                GenericSortCondition.createIdentityCondition(gs, s2);                                               
            if ( c == null ) {
                Debug.out("FAILED. Generic sort condition");
                return null; //FAILED;
            } else {
                try {                   
                    mc = mc
                    .setInstantiations ( mc.getInstantiations ().
                            add ( c ) );
                } catch ( SortException e ) {
                    Debug.out("FAILED. Sort mismatch.", s1, s2);
                    return null; //FAILED;
                }
            }                  
        }               
        return mc;
    }
    
    
    /**
     * Taking this sortdepending function as template to be matched against <code>op</code>, 
     * the necessary conditions are returned or null if not unifiable (matchable).
     * A sortdepending function is matched successfull against another sortdepending function
     * if the sorts can be matched and they are of same kind.      
     */
    public MatchConditions match(SVSubstitute subst, 
                                 MatchConditions mc,
                                 Services services) {      
        if (this.getClass() != subst.getClass()) {
            Debug.out("FAILED. Given operator cannot be matched by a sort" +
            		"depending function (template, orig)", this, subst);
            return null;
        }         
        final SortDependingFunction sdp = (SortDependingFunction)subst;
        final MatchConditions result = 
            matchSorts(getSortDependingOn(), sdp.getSortDependingOn(), mc);
        
        if (result == null) {
            Debug.out("Failed. Sorts of depending function not unifiable.", this, subst);
            return null;
        }
        
        return isSimilar(sdp) ? result : null;        
    }
}
