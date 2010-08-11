// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * Models an assignment pair <code> l_i := t_i </code>  of an update.
 * This data structure is only used for update simplification.
 */
public interface AssignmentPair {    

    /**
     * TODO: should guards and bound variables also be compared here???
     */
    public static class LocationAsKey {
        final AssignmentPair pair;
        
        public LocationAsKey(AssignmentPair pair) {        
            this.pair = pair;
        }
        
        public int hashCode() {
            return pair.locationHashCode();
        }
        
        public boolean equals(Object o) {     
            if (!(o instanceof LocationAsKey)) return false;
            return pair.equalLocations(((LocationAsKey)o).pair);
        }
        
        public AssignmentPair getAssignmentPair() {
            return pair;
        }          
    }
    
    /**
     * returns the location
     * @return the left side of the assignment
     */
    Term locationAsTerm();

    /**
     * returns the location operator
     * @return the location specifying operator
     */
    Location location();

    /**
     * returns the locations sub terms
     * @return the left side of the assignment
     */
    Term[] locationSubs();

    /** 
     * returns the value that is assigned to the location and adds
     * if necessary (i.e. the static type <code>T</code> of the location as term is not a 
     * supersort) a type cast <code> (T) </code> in front.
     * @return the right side of the assignment      
     */
    Term value();

    /** 
     * returns the value that is assigned to the location
     * without adding any cast. Use this method with care.
     * @return the right side of the assignment      
     */
    Term valueUnsafe();
    
    /**
     * The guard this update might have. This returns the formula <tt>true</tt>
     * in case of an unguarded assignment
     */
    Term guard();

    /**
     * If this returns <code>true</code> then one cannot assume that the guard
     * is valid (always true)
     */
    boolean nontrivialGuard();
    
    /**
     * Variables that be used to express parallel execution of
     * unboundedly/infinitely many updates
     * 
     * @return variables that are bound for this assignment pair
     */
    ImmutableArray<QuantifiableVariable> boundVars();
    
    /**
     * @return the set of quantifiable variables that turn up free in this
     *         assignment pair
     */
    ImmutableSet<QuantifiableVariable> freeVars();
    
    /**
     * compares the location of the given assignment pair with the
     * current location and returns true if they are equal
     * @param p the AssignmentPair whose location is compared
     * @return true if the location that is updated is equal to the location
     * of the given assignment pair
     */
    boolean equalLocations(AssignmentPair p);

    /**
     * TODO: must guards and bound variables also be considered at this point?
     * 
     * returns an int fulfilling the usual hashcode properties but
     * without consideration of the value part of the assignment pair
     * @return an int as location hashcode 
     */
    int locationHashCode();
}
