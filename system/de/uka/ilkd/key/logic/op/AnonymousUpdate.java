// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
/*
 * Created on 14.12.2004
 */
package de.uka.ilkd.key.logic.op;

import java.lang.ref.WeakReference;
import java.math.BigInteger;
import java.util.WeakHashMap;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;

/**
 * @author bubel
 */
public class AnonymousUpdate implements IUpdateOperator {

    private final Name name;
    
    private static WeakHashMap operatorPool = new WeakHashMap(20);
    private static BigInteger globalCounter = BigInteger.ZERO;
    
    
    /**
     *  
     */
    private AnonymousUpdate(Name name) {
        this.name = name;
    }

    /**
     * returns the anonymous update of the given name or creates a
     * new one if it does not exist
     * @param name the Name of the anon update operator to look for
     * @return the anonymous update operator
     */
    public static AnonymousUpdate getAnonymousOperator(Name name) {        
            WeakReference anonymousUpdateReference = 
                (WeakReference) operatorPool.get(name);
            if (anonymousUpdateReference == null
                    || anonymousUpdateReference.get() == null) {
                // wrapping attributeOp in a weak reference is necessary as
                // it contains a strong reference to its key
                anonymousUpdateReference = 
                       new WeakReference(new AnonymousUpdate(name));
                operatorPool.put(name, anonymousUpdateReference);
            }
            return (AnonymousUpdate) anonymousUpdateReference.get();
        } 
    
    /**
     * returns a new anonymous update 
     * @return a new anonymous update
     */
    public static AnonymousUpdate getNewAnonymousOperator() {        
        WeakReference anonymousUpdateReference = null;
        Name uniqueName; 
        do { 
             globalCounter = globalCounter.add(BigInteger.ONE);
             uniqueName = new Name("*:=*"+globalCounter);
             anonymousUpdateReference = 
                 (WeakReference) operatorPool.get(uniqueName);
         } while(anonymousUpdateReference != null);       
        // wrapping attributeOp in a weak reference is necessary as
        // it contains a strong reference to its key
        anonymousUpdateReference = 
            new WeakReference(new AnonymousUpdate(uniqueName));
        operatorPool.put(uniqueName, anonymousUpdateReference);        
        return (AnonymousUpdate) anonymousUpdateReference.get();
    }
    
    /** @return name of the operator */
    public Name name() {
        return name;
    }

    /**
     * returns the arity of the operator
     */
    public int arity() {
        return 1;
    }

    /**
     * returns the sort a term would have if constructed with this operator and
     * the given sunterms. It is assumed that the term would be allowed if
     * constructed.
     * 
     * @param term
     *            an array of Term containing the subterms of a (potential)
     *            simultaneous update term
     * @return sort of the simultaneous update term consisting of the given
     *         subterms, if this op would be the top symbol
     */
    public Sort sort(Term[] term) {
        return term[targetPos()].sort();
    }

    /**
     * @return true if the value of "term" having this operator as top-level
     *         operator and may not be changed by modalities
     */
    public boolean isRigid(Term term) {
	return true;
    }

    /**
     * checks whether the top level structure of the given {@link Term}is
     * syntactically valid, given the assumption that the top level operator of
     * the term is the same as this Operator. The assumption that the top level
     * operator and the operator are equal is NOT checked.
     * 
     * @return true iff the top level structure of the {@link Term}is valid.
     */
    public boolean validTopLevel(Term term) {
        return true;
    }

    public int entryBegin (int locPos) {
        Debug.fail("Method not implemented for anonymous update");
        return 0; // unreachable
    }
    
    public int entryEnd (int locPos) {
        Debug.fail("Method not implemented for anonymous update");
        return 0; // unreachable
    }

    public int[] getLocationPos (Operator loc) {
        Debug.fail("Method not implemented for anonymous update");
        return new int[0]; // unreachable
    }
    
    public Location location (int n) {
        Debug.fail("Method not implemented for anonymous update");
        return null; // unreachable
    }
    
    public Term location (Term t, int n) {
        Debug.fail("Method not implemented for anonymous update");
        return null; // unreachable
    }
    
    public int locationCount () {
        return 0;
    }
    
    public ImmutableArray<Location> locationsAsArray () {
        return new ImmutableArray<Location> ();
    }
    
    public int locationSubtermsBegin (int locPos) {
        Debug.fail("Method not implemented for anonymous update");
        return 0; // unreachable
    }
    
    public int locationSubtermsEnd (int locPos) {
        Debug.fail("Method not implemented for anonymous update");
        return 0; // unreachable
    }
    
    public IUpdateOperator replaceLocations (Location[] newLocs) {
        return this;
    }
    
    public Term value (Term t, int n) {
        Debug.fail("Method not implemented for anonymous update");
        return null; // unreachable
    }
    
    public int valuePos (int locPos) {
        Debug.fail("Method not implemented for anonymous update");
        return 0; // unreachable
    }
    
    /**
     * the position of the term the anonymous update is applied to  
     * @return the sub term position of the target term 
     */    
    public int targetPos () {
        return arity () - 1;
    }

    /**
     * @return the index of the subterm representing the formula/term the update
     *         is applied to
     */
    public Term target (Term t) {
        return t.sub ( targetPos () );
    }
    
    public MatchConditions match (SVSubstitute subst,
                                  MatchConditions mc,
                                  Services services) {
        if ( this == subst ) return mc;
        return null;
    }
    
    public String toString () {
        return "anonUpdate(" + name () + ")";
    }
}
