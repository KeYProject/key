// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
/*
 * Created on 26.11.2004
 */
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.util.Debug;

/**
 * The default implementation of an assignment pair.
 * There exists a lazy one to which may spare resources
 * @see AssignmentPairLazy
 * @author bubel
 */
public class AssignmentPairImpl implements AssignmentPair {

    private final Location accessOp;
    private final Term[] locSubs;
    private final Term value;
    
    /** 
     * caches the value part of the assignment pair 
     * (avoids repeated creation of casts) 
     */
    private Term safeValueCache = null; 
    
    private int cachedLocationHashCode;
    private final Term guard;
    private final ArrayOfQuantifiableVariable boundVars;
    private SetOfQuantifiableVariable freeVars = null;
    
    
    public AssignmentPairImpl (final ArrayOfQuantifiableVariable boundVars,
                               final Term guard,
                               final Location accessOp,
                               final Term[] locSubs,
                               final Term value) {
        this.boundVars = boundVars;
        this.guard = guard;
        this.accessOp = accessOp;
        this.locSubs = locSubs;
        this.value = value;
    }
    
    /**
     * creates the assignment <code>accessOp(locSubs):=value</code> 
     * @param accessOp the Location descriptor 
     * @param locSubs the subterms of the location
     * @param value the value the location is updated to
     */
    public AssignmentPairImpl (final Location accessOp,
                               final Term[] locSubs,
                               final Term value) {
        this ( new ArrayOfQuantifiableVariable (),
               UpdateSimplifierTermFactory.DEFAULT.getValidGuard(),
               accessOp,
               locSubs,
               value );
    }
        
    /**
     * 
     * returns the left side of the assignment pair as a term
     * 
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#locationAsTerm()
     */
    public Term locationAsTerm() {       
        return TermFactory.DEFAULT.createTerm(accessOp, locSubs,
                new ArrayOfQuantifiableVariable(), JavaBlock.EMPTY_JAVABLOCK);
    }

    /**
     * returns the location descriptor
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#location()
     */
    public Location location() {
        return accessOp;
    }

    /**
     * returns the sub terms of the location
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#locationSubs()
     */
    public Term[] locationSubs() {     
        return locSubs;
    }

    /**
     * returns the value the location is updated to
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#value()
     */
    public Term valueUnsafe() {
        return value;
    }
       
    
    /** 
     * returns the value that is assigned to the location and adds
     * if necessary (i.e. the static type <code>T</code> of the location as term is not a 
     * supersort) a type cast <code> (T) </code> in front.
     * @return the right side of the assignment      
     */
    public Term value() {
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

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#boundVars()
     */
    public ArrayOfQuantifiableVariable boundVars () {
        return boundVars;
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#freeVars()
     */
    public SetOfQuantifiableVariable freeVars () {
        if ( freeVars == null ) {
            freeVars = guard ().freeVars ().union ( value ().freeVars () );
            for ( int i = 0; i != locationSubs ().length; ++i )
                freeVars = freeVars.union ( locationSubs ()[i].freeVars () );

            for ( int i = 0; i != boundVars ().size (); ++i )
                freeVars = freeVars.remove ( boundVars ()
                                             .getQuantifiableVariable ( i ) );
        }
        
        return freeVars;
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#guard()
     */
    public Term guard () {
        return guard;
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#nontrivialGuard()
     */
    public boolean nontrivialGuard () {
        return guard ().op () != Op.TRUE;
    }
    
    /**
     * true if the locations of both assignment pairs are equal
     * 
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#equalLocations(de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair)
     */
    public boolean equalLocations(AssignmentPair p) {
        if (p.location() != accessOp) {
            return false;
        }
        Term[] cmpLocSubs = p.locationSubs();
        Debug.assertTrue(locSubs.length == cmpLocSubs.length);
        for (int i = 0; i < locSubs.length; i++) {
            if (!locSubs[i].equals(cmpLocSubs[i])) {
                return false;
            }
        }
        return true;
    }

    /**     
     * hashcode implementation
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#locationHashCode()
     */
    public int locationHashCode() {      
        if (cachedLocationHashCode == 0) {
            cachedLocationHashCode = accessOp.hashCode();
            for (int i = 0; i<locSubs.length; i++) {
                cachedLocationHashCode += 17*locSubs[i].hashCode();
            }        
            if (cachedLocationHashCode == 0) {
                cachedLocationHashCode = 1;
            }
        }        
        return cachedLocationHashCode;
    }

    /**
     * the hashCode of this assignment pair
     */
    public int hashCode () {
        return
            locationHashCode ()
            + 17 * valueUnsafe ().hashCode ()
            + 23 * guard ().hashCode ()
            + 31 * boundVars ().hashCode ();
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

    private String printBoundVars() {
        StringBuffer sb = new StringBuffer();
	QuantifiableVariable qvar = null;
	if(boundVars().size() == 1){
	   qvar = boundVars().getQuantifiableVariable(0);
	   if(qvar instanceof LogicVariable) {
	     sb.append(((LogicVariable)qvar).sort()+" "+((LogicVariable)qvar).name());
	   }else{
	     sb.append(qvar);
	   }
	   sb.append("; ");
	}else{
	   sb.append("(");
	   for(int i=0;i<boundVars().size();i++) {
	     qvar = boundVars().getQuantifiableVariable(i);
	     if(qvar instanceof LogicVariable) {
	       sb.append(((LogicVariable)qvar).sort()+" "+((LogicVariable)qvar).name());
	     }else{
	       sb.append(qvar);
	     }
	     if(i<boundVars().size()-1) {
		sb.append("; ");
	     }
	   }
	   sb.append(")");
	}
	return sb.toString();
    }

    public String toString() {
        return ""
            + ( boundVars().size() > 0 ? "\\for " + printBoundVars() + " " : "" )
            + ( nontrivialGuard() ? "\\if (" + guard() + ") " : "")
            + locationAsTerm() + ":=" + valueUnsafe();    
    }
    
}
