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
import de.uka.ilkd.key.logic.sort.oclsort.OclSort;

/** 
 * Represents the OCL operations: - and symmetricDifference() 
 */
public class OclDifference extends TermSymbol {
   
    public OclDifference(Name name) {
	super(name, OclSort.SET_OF_OCLANY);
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
	if (collSort0.getCollectionKind() != CollectionSort.SET
	    || collSort1.getCollectionKind() != CollectionSort.SET) {
	    return false;
	}
	if (!collSort0.getElemSort().extendsTrans(collSort1.getElemSort())
	    && !collSort1.getElemSort().extendsTrans(collSort0.getElemSort())) {
	    return false;
	}
        return true;
    }
    
    public Sort sort(Term[] subTerm) {	
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
	
	return CollectionSort.getCollectionSort(CollectionSort.SET, resultElemSort);
    }

    public String toString() {
	return (name() + ":"+OclSort.OCLGENERIC);
    }
    
    public String proofToString() {
       String s = OclSort.OCLGENERIC+" "+name();
       s+="(" + OclSort.BOOLEAN + ","
	   +OclSort.OCLGENERIC+","+OclSort.OCLGENERIC;
       s+=");\n";
       return s;
    }
}
