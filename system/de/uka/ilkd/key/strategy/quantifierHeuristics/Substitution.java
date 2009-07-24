// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ClashFreeSubst;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class decribes a substitution,which store a map(varMap) from quantifiable 
 * variable to a term(instance).
 */
class Substitution {

    private final TermBuilder tb = TermBuilder.DF;
    
    private MapFromQuantifiableVariableToTerm varMap;
    
    public Substitution(MapFromQuantifiableVariableToTerm map){
        varMap = map;
    }
    
    public MapFromQuantifiableVariableToTerm getVarMap(){
        return varMap;
    }
    
    public Term getSubstitutedTerm(QuantifiableVariable var){
    	return varMap.get(var);
    }
    
    public boolean isTotalOn(SetOfQuantifiableVariable vars) {
        IteratorOfQuantifiableVariable it = vars.iterator ();
        while ( it.hasNext () ) {
            if ( !varMap.containsKey ( it.next () ) ) return false;
        }
        return true;
    }
    

    /**
     * @return true if every instance in the varMap does not contain variable. 
     */
    public boolean isGround() {
        final IteratorOfQuantifiableVariable it = varMap.keyIterator ();
        while ( it.hasNext () ) {
            if ( getSubstitutedTerm( it.next () ).freeVars ().size () != 0 )
                return false;
        }
        return true;
    }   
  
    
    public Term apply(Term t, Services services) {
        assert isGround() :
            "non-ground substitutions are not yet implemented";
        final IteratorOfQuantifiableVariable it = varMap.keyIterator ();
        while ( it.hasNext () ) {
            final QuantifiableVariable var = it.next ();
            final Sort quantifiedVarSort = var.sort ();
            final Function quantifiedVarSortCast =
                quantifiedVarSort.getCastSymbol (services);
            Term instance = getSubstitutedTerm( var );
            if ( !instance.sort ().extendsTrans ( quantifiedVarSort ) )
            	instance = tb.func ( quantifiedVarSortCast, instance );
            t = applySubst ( var, instance, t );
        }
        return t;
    }

    private Term applySubst(QuantifiableVariable var, Term instance, Term t) {
        final ClashFreeSubst subst = new ClashFreeSubst ( var,  instance);
        return subst.apply ( t );
    }
    
    /**
     * Try to apply the substitution to a term, widening by removing casts to
     * jbyte, jint whenever possible 
     */
    public Term applyWithoutCasts(Term t, Services services) {
        assert isGround() :
            "non-ground substitutions are not yet implemented";
        final IteratorOfQuantifiableVariable it = varMap.keyIterator ();
        while ( it.hasNext () ) {
            final QuantifiableVariable var = it.next ();
            Term instance = getSubstitutedTerm( var );
            
            try {
                t = applySubst ( var, instance, t );
            } catch (TermCreationException e) {
                final Sort quantifiedVarSort = var.sort ();
                if ( !instance.sort ().extendsTrans ( quantifiedVarSort ) ) {
                    final Function quantifiedVarSortCast =
                        quantifiedVarSort.getCastSymbol (services);
                    instance = tb.func ( quantifiedVarSortCast, instance );
                    t = applySubst ( var, instance, t );
                } else {
                    throw e;
                }
            }        
        }
        return t;
    }
    
    public boolean equals(Object arg0) {
        if ( !(arg0 instanceof Substitution) ) return false;
        final Substitution s = (Substitution)arg0;
        return varMap.equals(s.varMap);
    }

    public int hashCode() {
        return varMap.hashCode();
    }
    
    public String toString() {
    	return "" + varMap;
    }
    
    public boolean termContainsValue(Term term) {
        IteratorOfTerm it = varMap.valueIterator ();
        while ( it.hasNext () ) {
            if ( recOccurCheck ( it.next (), term ) ) return true;
        }
        return false;
    }

    /**
     * check whether term "sub" is in term "term"
     */
    private boolean recOccurCheck(Term sub, Term term) {
        if ( sub.equals ( term ) ) return true;
        for ( int i = 0; i < term.arity (); i++ ) {
            if ( recOccurCheck ( sub, term.sub ( i ) ) ) return true;
        }
        return false;
    }
}
