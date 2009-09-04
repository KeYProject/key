// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;


/**
 * Replaces operators in a term by other operators with the same signature, 
 * or subterms of the term by other terms with the same sort. Does not 
 * replace in java blocks.
 */
public class OpReplacer {
    private static final TermFactory TF = TermFactory.DEFAULT;
    
    private final Map /*Operator -> Operator, Term -> Term*/ map;
    
    
    /**
     * @param map mapping from the operators/terms to be replaced to the ones to 
     * replace them with
     */
    public OpReplacer(Map /*Operator -> Operator, Term -> Term*/ map) {
	assert map != null;
        this.map = map;
    }
    
    
    public static Term replace(Term toReplace, Term with, Term in) {
	Map map = new HashMap();
	map.put(toReplace, with);
	OpReplacer or = new OpReplacer(map);
	return or.replace(in);
    }
    
    
    /**
     * Replaces in an operator.
     */
    public Operator replace(Operator op) {
        Operator newOp = (Operator) map.get(op);
        if(newOp != null) {
            return newOp;
        } else {
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
        
        final Term newTerm = (Term) map.get(term); 
        if(newTerm != null) {
            return newTerm;
        }

        final Operator newOp = replace(term.op());
        
        final int arity = term.arity();
        final Term newSubTerms[] = new Term[arity];    
        boolean changedSubTerm = false;
        for(int i = 0; i < arity; i++) {
            Term subTerm = term.sub(i);
            newSubTerms[i] = replace(subTerm);
    
            if(newSubTerms[i] != subTerm) {
                changedSubTerm = true;
            }
        }
        
        final ImmutableArray<QuantifiableVariable> newBoundVars 
        	= replace(term.boundVars());
    
        final Term result;
        if(newOp != term.op()  
           || changedSubTerm
           || newBoundVars != term.boundVars()) {
            result = TF.createTerm(newOp,
                                   newSubTerms,
                                   newBoundVars,
                                   term.javaBlock());
        } else {
            result = term;
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
    public Map<Operator, Term> replace(/*in*/ Map<Operator, Term> map) {
        
        Map<Operator,Term> result = new HashMap<Operator, Term>();
        
        final Iterator<Map.Entry<Operator, Term>> it = map.entrySet().iterator();
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
