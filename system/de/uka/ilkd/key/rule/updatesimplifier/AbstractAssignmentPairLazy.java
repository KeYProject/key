// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;
import de.uka.ilkd.key.logic.sort.AbstractSort;


/**
 *
 */
abstract class AbstractAssignmentPairLazy implements AssignmentPair {

    /**
     * term with the update operator as top level operator to which the modeled assignment pair belongs 
     */
    private final Term update;
    private SetOfQuantifiableVariable freeVars = null;

    /**
     * stores the location hash code 
     */
    private int locationHash = 0;
    
    /**
     *  caches the value part of the assignment pair 
     * (avoids repeated creation of casts) 
     */
    private Term safeValueCache = null; 

    /**
     * caches created terms denoting the locations 
     */
    private Term[] locationSubsCache = null;
    private int subtermsBeginCache = -1;
    private int subtermsEndCache = -1;

    
    protected AbstractAssignmentPairLazy (final Term update, int locationPos) {
        this.update = update;
        this.locationPos = locationPos;
    }
    
    protected Term getUpdateTerm () {
        return update;
    }

    protected IUpdateOperator getUpdateOp () {
        return (IUpdateOperator)getUpdateTerm ().op ();
    }

    /**
     * the position <code> i </code> of the location in the update operator 
     */
    private final int locationPos;

    protected int getLocationPos () {
        return locationPos;
    }

    /**
     * returns the location
     * @return  the left side of the assignment
     */
    public Term locationAsTerm () {
        return getUpdateOp ().location ( getUpdateTerm (), getLocationPos () );
    }

    /**
     * returns the location operator
     * @return  the location specifying operator
     */
    public Location location () {
        return getUpdateOp ().location ( getLocationPos () );
    }


    /**
     * returns the locations sub terms
     * @return  the left side of the assignment
     */
    public Term[] locationSubs () {
	if ( locationSubsCache == null ) {
	    locationSubsCache = new Term [location ().arity ()];
	    for ( int i = 0, j = locationSubtermsBegin ();
		  j != locationSubtermsEnd ();
		  ++i, ++j )
		locationSubsCache[i] = getUpdateTerm ().sub ( j );
	}
        return locationSubsCache;
    }

    protected int locationSubtermsBegin () {
	if ( subtermsBeginCache == -1 )
	    subtermsBeginCache =
		getUpdateOp ().locationSubtermsBegin ( getLocationPos () );
	return subtermsBeginCache;
    }

    protected int locationSubtermsEnd () {
	if ( subtermsEndCache == -1 )
	    subtermsEndCache =
		getUpdateOp ().locationSubtermsEnd ( getLocationPos () );
	return subtermsEndCache;
    }
  

    /**
     * returns an int fulfilling the usual hashcode properties but without
     * consideration of the value part of the assignment pair
     * 
     * @return an int as location hashcode
     */
    public int locationHashCode () {
        if ( locationHash == 0 ) {
            locationHash = location ().hashCode ();
            final Term[] locSubs = locationSubs ();
            for ( int i = 0; i < locSubs.length; i++ ) {
                locationHash += 17 * locSubs[i].hashCode ();
            }
            if ( locationHash == 0 ) {
                locationHash = 1;
            }
        }
        return locationHash;
    }

    /**
     * returns true if the location that is updated is equal to location of the
     * given assignment pair
     * 
     * @param p
     *            the AssignmentPair whose location is compared
     * @return true if the location that is updated is equal to location of the
     *         given assignment pair
     */
    public boolean equalLocations (AssignmentPair p) {
        if ( p.location () != location () ) return false;

        final Term[] pLocSubs = p.locationSubs ();
        final Term[] tLocSubs = this.locationSubs ();

        if ( pLocSubs.length != tLocSubs.length ) return false;

        for ( int i = 0; i < pLocSubs.length; i++ ) {
            if ( !( pLocSubs[i].equals ( tLocSubs[i] ) ) ) return false;
        }
        return true;
    }   
    
    /** 
     * returns the value that is assigned to the location and adds
     * if necessary (i.e. the static type <code>T</code> of the location as term is not a 
     * supersort) a type cast <code> (T) </code> in front.
     * @return the right side of the assignment      
     */
    public Term value () {
        if (safeValueCache == null) {
            safeValueCache = valueUnsafe();            
            final AbstractSort s = (AbstractSort)locationAsTerm().sort();
            if (!(safeValueCache.sort().extendsTrans(s))) {
                safeValueCache = 
                    TermFactory.DEFAULT.createFunctionTerm(s.getCastSymbol(), safeValueCache);
            }
        }
        return safeValueCache;
    }
    
    /**
     * returns the value that is assigned to the location
     * (no implicit casts are added and therefore themethod is not type safe)
     * You should be sure what you are doing if using this method, otherwise 
     * {@link AbstractAssignmentPairLazy#value}
     * @return  the right side of the assignment      
     */
    public Term valueUnsafe () {
        return getUpdateTerm ().sub ( valuePos () );
    }

    protected int valuePos () {
        return getUpdateOp ().valuePos ( getLocationPos () );
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#freeVars()
     */
    public SetOfQuantifiableVariable freeVars () {
        if ( freeVars == null ) {
            freeVars = guard ().freeVars ().union ( valueUnsafe ().freeVars () );
            for ( int i = 0; i != locationSubs ().length; ++i )
                freeVars = freeVars.union ( locationSubs ()[i].freeVars () );

            for ( int i = 0; i != boundVars ().size (); ++i )
                freeVars = freeVars.remove ( boundVars ()
                                             .getQuantifiableVariable ( i ) );
        }
        
        return freeVars;
    }

    public String toString() {
        return ""
            + ( boundVars().size() > 0 ? "\\for " + boundVars() + " " : "" )
            + ( nontrivialGuard() ? "\\if (" + guard() + ") " : "")
            + locationAsTerm() + ":=" + valueUnsafe();    
    }

    /**
     * returns true if the given object equals this one
     */
    public boolean equals (Object o) {
        if ( !( o instanceof AssignmentPair ) ) return false;

        final AssignmentPair p = (AssignmentPair)o;

        return equalLocations ( p )
               && p.valueUnsafe ().equals ( valueUnsafe () )
               && p.guard ().equals ( guard () )
               && boundVars ().equals ( boundVars () );
    }

    /**
     * the hashCode of this assignment pair
     */
    public int hashCode () {
        return
            locationHashCode ()
            + 17 * value ().hashCode ()
            + 23 * guard ().hashCode ()
            + 31 * boundVars ().hashCode ();
    }
}
