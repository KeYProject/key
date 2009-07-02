// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.*;


/**
 * This class represents an equality symbol for a given sort.
 * The system will generate automatically for each sort exactly one 
 * equality symbol. For the special sort Formula the corresponding equality 
 * symbol is the equivalence-junctor {@link Equality#EQV}.
 */
public final class Equality extends Op {

    private final Sort targetSort;

    /** 
     * the ususal 'equality' operator '=' 
     */
    public static final Equality EQUALS = new Equality(new Name("equals"), 
	    					       Sort.ANY);
    
    /** 
     * the ususal 'equivalence' operator '<->' (be A, B formulae then       
     * 'A <->  B' is true if and only if A and B have the same truth
     * value 
     */ 
    public static final Equality EQV = new Equality(new Name("equiv"),
        					    Sort.FORMULA);
    
    
    private Equality(Name name, Sort targetSort){
	super(name, 2);
	assert targetSort != null : "creating " + name + " failed";
	this.targetSort = targetSort;
    }


    public Sort sort(Term[] term) {
	return Sort.FORMULA;
    }

    /** 
     * returns the sort of the <tt>i</tt>-th argument
     */
    public Sort argSort(int i) {
	return targetSort;
    }

    
    /**
     * checks if the given term is syntactically valid at its top
     * level assumed the top level operator were this, i.e. if the
     * direct subterms can be subterms of a term with this top level
     * operator, the method returns true. Furthermore, it is checked
     * that no variables are bound for none of the subterms.
     * If a subterm is a schemavariable, the whole term is accepted.
     * @param term the Term to be checked.  
     * @return true iff the given term has
     * subterms that are suitable for this function.
     */
    public boolean validTopLevel(Term term){
	if (term.arity()!=arity()) {
	    return false;
	}
	
	for (int i=0; i<arity(); i++) {
	    Sort sort = term.sub(i).sort();
	    if (term.sub(i).op() instanceof SchemaVariable ||
		sort instanceof ProgramSVSort || 
		sort == AbstractMetaOperator.METASORT) {
		return true;
	    }   
	}
        
	final Sort t0Sort = term.sub(0).sort();
	final Sort t1Sort = term.sub(1).sort();

	/*
	if (t0Sort instanceof PrimitiveSort != t1Sort instanceof PrimitiveSort) {
	    return false;
	}*/	

	if ( targetSort == Sort.FORMULA || t0Sort == Sort.FORMULA || t1Sort == Sort.FORMULA ) { 
	    return t0Sort == Sort.FORMULA && t1Sort == Sort.FORMULA && targetSort == Sort.FORMULA;
	}
	
	return t0Sort.extendsTrans(targetSort) && t1Sort.extendsTrans(targetSort);
    }
    
}

