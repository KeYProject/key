// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.sort.oclsort.OclSort;

/**
 * Represents the OCL operations: append(), prepend()
 */
public class OclSequenceOp extends TermSymbol {
   
    public OclSequenceOp(Name name) {
	super(name, OclSort.SEQUENCE_OF_OCLANY);
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
	if (!(term.sub(0).sort() instanceof CollectionSort)) {
	    return false;
	}
	CollectionSort collSort = (CollectionSort)term.sub(0).sort();
	if (!collSort.extendsTrans(OclSort.SEQUENCE_OF_OCLANY)) {
	    return false;
	}
	OclSort elemSort = (OclSort)term.sub(1).sort();
	if (!collSort.getElemSort().extendsTrans(elemSort)
	    && !elemSort.extendsTrans(collSort.getElemSort())) {
	    return false;
	}
        return true;
    }
    
    public Sort sort(Term[] subTerm) {
	if (subTerm.length != arity()) {
	    throw new IllegalArgumentException("Cannot determine sort of "+
						"invalid term (Wrong arity).");
	}
	if (!(subTerm[0].sort() instanceof CollectionSort)) {
	    throw new IllegalArgumentException("Cannot determine sort of "+
						"invalid term (First argument must be a Collection).");
	}
	
	OclSort resultElemSort = null;
	OclSort elemSort0 
	    = ((CollectionSort)subTerm[0].sort()).getElemSort();
	OclSort elemSort1 = (OclSort)subTerm[1].sort();
	if (elemSort0.extendsTrans(elemSort1)) {
	    resultElemSort = elemSort1; 
	} else if (elemSort1.extendsTrans(elemSort0)) {
	    resultElemSort = elemSort0;
	} else {
	    throw new IllegalArgumentException("Cannot determine sort of "+
						"invalid term (Arguments must have a common supersort).");
	}
	
	return CollectionSort
	    .getCollectionSort(CollectionSort.SEQUENCE,
			       resultElemSort);
    }
  
    public String toString() {
	return (name()+":"+OclSort.SEQUENCE_OF_OCLANY);
    }
    
    public String proofToString() {
       String s = OclSort.SEQUENCE_OF_OCLANY+" "+name();
       s+="(" + OclSort.SEQUENCE_OF_OCLANY + ", " + OclSort.OCLANY;
       s+=");\n";
       return s;
    }
}
