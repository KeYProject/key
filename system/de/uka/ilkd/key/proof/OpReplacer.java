// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.*;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Operator;
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
        
        Term newTerm = (Term) map.get(term); 
        if(newTerm != null) {
            return newTerm;
        }

        Operator newOp = replace(term.op());
        
        int arity = term.arity();
        Term newSubTerms[] = new Term[arity];
        ArrayOfQuantifiableVariable[] boundVars =
                new ArrayOfQuantifiableVariable[arity];
    
        boolean changedSubTerm = false;
        for(int i = 0; i < arity; i++) {
            Term subTerm = term.sub(i);
            newSubTerms[i] = replace(subTerm);
            
            // Is it guaranteed that no variables are renamed in the replaced term?
            boundVars[i] = term.varsBoundHere(i);
    
            if(newSubTerms[i] != subTerm) {
                changedSubTerm = true;
            }
        }
    
        Term result = term;
        
        if(newOp != term.op() || changedSubTerm) {
            result = TF.createTerm(newOp,
                                   newSubTerms,
                                   boundVars,
                                   term.javaBlock());
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
     * Replaces in a list of terms.
     */
    public ListOfTerm replace(ListOfTerm terms) {
        ListOfTerm result = SLListOfTerm.EMPTY_LIST;
        for (final Term term : terms) {
            result = result.append(replace(term));
        }
        return result;
    }

    /**
     * Replaces in a location descriptor.
     */
    public LocationDescriptor replace(LocationDescriptor loc) {
        if(loc == null) {
            return null;
        } else if(loc instanceof BasicLocationDescriptor) {
            BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
            return new BasicLocationDescriptor(replace(bloc.getFormula()), 
                                               replace(bloc.getLocTerm()));
        } else {
            assert loc instanceof EverythingLocationDescriptor;
            return loc;
        }
    }
    
    
    /**
     * Replaces in a set of location descriptors.
     */
    public SetOfLocationDescriptor replace(SetOfLocationDescriptor locs) {
	SetOfLocationDescriptor result 
		= SetAsListOfLocationDescriptor.EMPTY_SET;
	for (final LocationDescriptor loc : locs) {
	    result = result.add(replace(loc));
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
}
