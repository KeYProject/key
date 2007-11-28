// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.sort.oclsort.CollectionSort;
import de.uka.ilkd.key.logic.sort.oclsort.OclAnySort;
import de.uka.ilkd.key.logic.sort.oclsort.OclSort;

/**
 * Represents an OCL Sequence.
 * All OCL collections are built using two list-like
 * constructors, empty<T>() and insert<T>(elem, collection),
 * where <T> is either Set, Bag, or Sequence.
 */
public class OclInsertSequence extends TermSymbol {
       
    public OclInsertSequence() {
	super(new Name("$insert_sequence"), OclSort.SEQUENCE_OF_OCLANY);
    }
    
    /** @return arity of the Function as int */
    public int arity() {
	return 2;
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
	if (term.varsBoundHere(0).size()!=0
	    || term.varsBoundHere(1).size()!=0) {
	    return false; 
	}

	/* $insert_set(1, $insert_set(2, $empty)) */
	if (!(term.sub(1).sort() instanceof CollectionSort)) {
	    return false;
	}
	CollectionSort collSort = (CollectionSort)term.sub(1).sort();
	if (collSort.getCollectionKind() != CollectionSort.SEQUENCE) {
	    return false;
	}
	if (!term.sub(0).sort().extendsTrans(collSort.getElemSort())) {
	    return false;
	}
	
        return true;
    }

    public Sort sort(Term[] subTerm) {
	OclAnySort elemSort = (OclAnySort)subTerm[0].sort();
	return CollectionSort
	    .getCollectionSort(CollectionSort.SEQUENCE,
			       elemSort);
    }

    public String toString() {
	return (name()+":"+OclSort.SEQUENCE_OF_OCLANY);
    }
    
    public String proofToString() {
       String s = OclSort.SEQUENCE_OF_OCLANY+" "+name();
       s+="("+OclSort.OCLANY+","+OclSort.SEQUENCE_OF_OCLANY;
       s+=");\n";
       return s;
    }
}
