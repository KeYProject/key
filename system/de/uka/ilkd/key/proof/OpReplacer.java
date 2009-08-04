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

import de.uka.ilkd.key.logic.SetAsListOfTerm;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;


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
        
        final ArrayOfQuantifiableVariable newBoundVars 
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
    public SetOfTerm replace(SetOfTerm terms) {
        SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
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
     * Replaces in a FormulaWithAxioms.
     */
    public FormulaWithAxioms replace(FormulaWithAxioms fwa) {
        return new FormulaWithAxioms(replace(fwa.getFormula()), 
                                     replace(fwa.getAxioms()));
    }
    
    
    /**
     * Replaces in an ArrayOfQuantifiableVariable.
     */
    public ArrayOfQuantifiableVariable replace(
	    			ArrayOfQuantifiableVariable vars) {
	QuantifiableVariable[] result = new QuantifiableVariable[vars.size()];
	boolean changed = false;
	for(int i = 0, n = vars.size(); i < n; i++) {
	    QuantifiableVariable qv = vars.getQuantifiableVariable(i);
	    QuantifiableVariable newQv = (QuantifiableVariable)replace(qv);
	    result[i++] = newQv;
	    if(newQv != qv) {
		changed = true;
	    }
	}
	return changed ? new ArrayOfQuantifiableVariable(result) : vars;
    }
}
