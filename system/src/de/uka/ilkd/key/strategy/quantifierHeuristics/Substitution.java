// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ClashFreeSubst;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;

/**
 * This class decribes a substitution,which store a map(varMap) from quantifiable 
 * variable to a term(instance).
 */
public class Substitution {

    private final TermBuilder tb = TermBuilder.DF;
    
    private final ImmutableMap<QuantifiableVariable,Term> varMap;
    
    public Substitution(ImmutableMap<QuantifiableVariable,Term> map){
        varMap = map;
    }
    
    public ImmutableMap<QuantifiableVariable,Term> getVarMap(){
        return varMap;
    }
    
    public Term getSubstitutedTerm(QuantifiableVariable var){
    	return varMap.get(var);
    }
    
    public boolean isTotalOn(ImmutableSet<QuantifiableVariable> vars) {
        for (QuantifiableVariable var : vars) {
            if (!varMap.containsKey(var)) return false;
        }
        return true;
    }
    

    /**
     * @return true if every instance in the varMap does not contain variable. 
     */
    public boolean isGround() {
        final Iterator<QuantifiableVariable> it = varMap.keyIterator ();
        while ( it.hasNext () ) {
            final Term t = getSubstitutedTerm(it.next ()); 
            if ( t.freeVars ().size () != 0 ) {
            	Debug.out("evil free vars in term: " + t);
                return false;
            }
        }
        return true;
    }   
  
    
    public Term apply(Term t, Services services) {
        assert isGround() :
            "non-ground substitutions are not yet implemented: " + this;
        final Iterator<QuantifiableVariable> it = varMap.keyIterator ();
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
     * Try to apply the substitution to a term, introducing casts if
     * necessary (may never be the case any more, XXX)
     */
    public Term applyWithoutCasts(Term t, Services services) {
        assert isGround() :
            "non-ground substitutions are not yet implemented: " + this;
        final Iterator<QuantifiableVariable> it = varMap.keyIterator ();
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
        Iterator<Term> it = varMap.valueIterator ();
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
