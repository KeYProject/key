// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.Map;

import de.uka.ilkd.key.logic.BasicLocationDescriptor;
import de.uka.ilkd.key.logic.IteratorOfLocationDescriptor;
import de.uka.ilkd.key.logic.LocationDescriptor;
import de.uka.ilkd.key.logic.SetAsListOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Operator;


/**
 * Replaces operators in a term by other operators with the same signature, 
 * or subterms of the term by other terms with the same sort.
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
     * Replaces in a term.
     */
    public Term replace(Term term) {
        Term newTerm = (Term) map.get(term); 
        if(newTerm != null) {
            return newTerm;
        }
        
        Operator newOp = (Operator) map.get(term.op());
        if(newOp == null) {
            newOp = term.op();
        }
        
        int arity = term.arity();
        Term newSubTerms[] = new Term[arity];
        ArrayOfQuantifiableVariable[] boundVars =
                new ArrayOfQuantifiableVariable[arity];
    
        boolean changedSubTerm = false;
        for(int i = 0; i < arity; i++) {
            Term subTerm = term.sub(i);
            newSubTerms[i] = replace(subTerm);
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
     * Replaces in a location descriptor.
     */
    public LocationDescriptor replace(LocationDescriptor loc) {
        if(loc instanceof BasicLocationDescriptor) {
            BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
            return new BasicLocationDescriptor(replace(bloc.getFormula()), 
                                               replace(bloc.getLocTerm()));
        } else {
            return loc;
        }
    }
    
    
    /**
     * Replaces in a set of location descriptors.
     */
    public SetOfLocationDescriptor replace(SetOfLocationDescriptor locs) {
	SetOfLocationDescriptor result 
		= SetAsListOfLocationDescriptor.EMPTY_SET;
	IteratorOfLocationDescriptor it = locs.iterator();
	while(it.hasNext()) {
	    result = result.add(replace(it.next()));
	}
	return result;
    }
}
