// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;


/**
 * Replaces operators in a term by other operators with the same signature, 
 * or subterms of the term by other terms with the same sort. Does not 
 * replace in java blocks.
 */
public class OpReplacer {
    private static final TermFactory TF = TermFactory.DEFAULT;

    private final Map<? extends SVSubstitute, ? extends SVSubstitute> map;


    /**
     * @param map mapping from the operators/terms to be replaced to the ones to 
     * replace them with
     */
    public OpReplacer(Map<? extends SVSubstitute, ? extends SVSubstitute> map) {
	assert map != null;
        this.map = map;
    }
    
    
    public static Term replace(Term toReplace, Term with, Term in) {
	Map<Term,Term> map = new HashMap<Term,Term>();
	map.put(toReplace, with);
	OpReplacer or = new OpReplacer(map);
	return or.replace(in);
    }
    
    
    public static ImmutableList<Term> replace(Term toReplace, 
	                                      Term with, 
	                                      ImmutableList<Term> in) {
	Map<Term,Term> map = new HashMap<Term,Term>();
	map.put(toReplace, with);
	OpReplacer or = new OpReplacer(map);
	return or.replace(in);
    }    
    
    
    
    public static Term replace(Operator toReplace, Operator with, Term in) {
	Map<Operator,Operator> map = new HashMap<Operator,Operator>();
	map.put(toReplace, with);
	OpReplacer or = new OpReplacer(map);
	return or.replace(in);
    }    
    
    
    /**
     * Replaces in an operator.
     */
    public Operator replace(Operator op) {
        System.out.println("Mapping: " + map.toString()); // TODO: for debugging, to be removed
        Operator newOp = (Operator) map.get(op);        
        System.out.println("Found? " + map.containsKey(op)); // TODO: for debugging, to be removed
        System.out.println("Old Operator " + op.toString()); // TODO: for debugging, to be removed
        if(newOp != null) {
            System.out.println("New Operator: " + newOp.toString()); // TODO: for debugging, to be removed
            return newOp;
        } else {
            System.out.println("No new Operator."); // TODO: for debugging, to be removed
            return op;
        }
    }
    
    
    /**
     * Replaces in a term.
     */
    public Term replace(Term term) {
        if(term == null) {
            return null;
        }
        System.out.println("Term: " + term.toString()); // TODO: for debugging, to be removed
        final Term newTerm = (Term) map.get(term); 
        if(newTerm != null) {
            System.out.println("New Term! " + newTerm.toString()); // TODO: for debugging, to be removed
            return newTerm;
        }

        final Operator newOp = replace(term.op());
        
        final int arity = term.arity();
        final Term newSubTerms[] = new Term[arity];    
        boolean changedSubTerm = false;
        for(int i = 0; i < arity; i++) {
            Term subTerm = term.sub(i);
            System.out.println("Subterm " + i + ": " + subTerm.toString() + " ..."); // TODO: for debugging, to be removed          
            newSubTerms[i] = replace(subTerm);
            System.out.println("... becomes " + i + ": " + newSubTerms[i].toString()); // TODO: for debugging, to be removed
    
            if(newSubTerms[i] != subTerm) {
                changedSubTerm = true;
            }
        }
        
        final ImmutableArray<QuantifiableVariable> newBoundVars 
        	= replace(term.boundVars());
    
        if (newOp != term.op())
            System.out.println("Operator! " + newOp.toString()); // TODO: for debugging, to be removed
        else if (changedSubTerm)
            System.out.println("Subterm!"); // TODO: for debugging, to be removed
        else if (newBoundVars != term.boundVars())
            System.out.println("Bounded Variables! " + newBoundVars.toString()); // TODO: for debugging, to be removed
        else
            System.out.println("No success! " + term.toString()); // TODO: for debugging, to be removed
        final Term result;
        if(newOp != term.op()  
           || changedSubTerm
           || newBoundVars != term.boundVars()) {
            result = TF.createTerm(newOp,
                                   newSubTerms,
                                   newBoundVars,
                                   term.javaBlock());
            System.out.println("Term created! "  + result.toString()); // TODO: for debugging, to be removed
        } else {
            result = term;
        }
    
        return result;
    }      
    
    /**
     * Replaces in a list of terms.
     */
    public ImmutableList<Term> replace(ImmutableList<Term> terms) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for(final Term term : terms) {
            result = result.append(replace(term));
        }
        return result;
    }    
    
    
    /**
     * Replaces in a set of terms.
     */
    public ImmutableSet<Term> replace(ImmutableSet<Term> terms) {
        ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        for (final Term term : terms) {
            result = result.add(replace(term));
        }
        return result;
    }

    
    /**
     * Replaces in a map from Operator to Term.
     */
    public Map<Operator, Term> replace(/*in*/ Map<Operator, Term> myMap) {
        
        Map<Operator,Term> result = new HashMap<Operator, Term>();
        
        final Iterator<Map.Entry<Operator, Term>> it = myMap.entrySet().iterator();
        while(it.hasNext()) {
            final Map.Entry<Operator, Term> entry = it.next();
            result.put(replace(entry.getKey()), replace(entry.getValue()));
        }        
        return result;
    }
    
   
    /**
     * Replaces in an ImmutableArray<QuantifiableVariable>.
     */
    public ImmutableArray<QuantifiableVariable> replace(
	    			ImmutableArray<QuantifiableVariable> vars) {
	QuantifiableVariable[] result = new QuantifiableVariable[vars.size()];
	boolean changed = false;
	for(int i = 0, n = vars.size(); i < n; i++) {
	    QuantifiableVariable qv = vars.get(i);
	    QuantifiableVariable newQv = (QuantifiableVariable)replace(qv);
	    result[i++] = newQv;
	    if(newQv != qv) {
		changed = true;
	    }
	}
	return changed ? new ImmutableArray<QuantifiableVariable>(result) : vars;
    }
}
