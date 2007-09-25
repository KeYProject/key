// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.op.oclop;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.TermSymbol;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.oclsort.OclSort;

/**
 * Represents an empty OCL Set.
 * All OCL collections are built using two list-like
 * constructors, empty<T>() and insert<T>(elem, collection),
 * where <T> is either Set, Bag, or Sequence.
 */
public class OclEmptySet extends TermSymbol {
       
    public OclEmptySet() {
	super(new Name("$empty_set"), OclSort.SET_OF_OCLANY);
    }
    
    /** @return arity of the Function as int */
    public int arity() {
	return 0;
    }


    /*
     * checks if the given term is syntactically valid at its top
     * level assumed the top level operator were this, i.e. if the
     * direct subterms can be subterms of a term with this top level
     * operator, the method returns true. Furthermore, it is checked
     * that no variables are bound for none of the subterms.  
     * @param the Term to be checked.  
     * @return true iff the given term has
     * subterms that are suitable for this function.
     */
    public boolean validTopLevel(Term term){
	if (term.arity()!=arity()) {
	    return false;
	}
	
        return true;
    }

    public Sort sort(Term[] subTerm) {
	return OclSort.SET_OF_OCLGENERIC;
    }
  
    public String toString() {
	return (name()+":"+OclSort.SET_OF_OCLANY);
    }
    
    public String proofToString() {
       String s = OclSort.SET_OF_OCLANY+" "+name();
       s+="(";
       s+=");\n";
       return s;
    }
}
