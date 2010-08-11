// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
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
 * Represents the OCL operation: intersection()
 */
public class OclIntersection extends TermSymbol {
   
    public OclIntersection() {
	super(new Name("$intersection"), OclSort.COLLECTION_OF_OCLANY);
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
	if (!(term.sub(0).sort() instanceof CollectionSort)
	    || !(term.sub(1).sort() instanceof CollectionSort)) {
	    return false;
	}
	CollectionSort collSort0 = (CollectionSort)term.sub(0).sort();
	CollectionSort collSort1 = (CollectionSort)term.sub(1).sort();
	if (collSort0.getCollectionKind() == CollectionSort.SEQUENCE
	    || collSort1.getCollectionKind() == CollectionSort.SEQUENCE) {
	    return false;
	}
        return !(!collSort0.getElemSort().extendsTrans(collSort1.getElemSort())
                && !collSort1.getElemSort().extendsTrans(collSort0.getElemSort()));
    }
    
    public Sort sort(Term[] subTerm) {
	if (subTerm.length != arity()) {
	    throw new IllegalArgumentException("Cannot determine sort of "+
						"invalid term (Wrong arity).");
	}
	if (!(subTerm[0].sort() instanceof CollectionSort)
	    || !(subTerm[1].sort() instanceof CollectionSort)) {
	    throw new IllegalArgumentException("Cannot determine sort of "+
						"invalid term (Both args must be Collections).");
	}
	int resultCollKind = -1;
	int collKind0 
	    = ((CollectionSort)subTerm[0].sort()).getCollectionKind();
	int collKind1 
	    = ((CollectionSort)subTerm[1].sort()).getCollectionKind();
	if (collKind0 == CollectionSort.BAG
	    && collKind1 == CollectionSort.BAG) {
	    resultCollKind = CollectionSort.BAG;
	} else if (collKind0 == CollectionSort.SET
		   || collKind1 == CollectionSort.SET) {
	    resultCollKind = CollectionSort.SET;
	} 
	
	OclSort resultElemSort = null;
	OclSort elemSort0 
	    = ((CollectionSort)subTerm[0].sort()).getElemSort();
	OclSort elemSort1 
	    = ((CollectionSort)subTerm[1].sort()).getElemSort();
	if (elemSort0.extendsTrans(elemSort1)) {
	    resultElemSort = elemSort1; 
	} else {
	    resultElemSort = elemSort0;
	}
	
	return CollectionSort.getCollectionSort(resultCollKind, resultElemSort);
    }
  
    public String toString() {
	return (name()+":"+OclSort.OCLGENERIC);
    }
    
    public String proofToString() {
       String s = OclSort.OCLGENERIC+" "+name();
       s+="(" + OclSort.BOOLEAN + ","+OclSort.OCLGENERIC
	   +","+OclSort.OCLGENERIC;
       s+=");\n";
       return s;
    }
}
