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
 * Represents the OCL operations: asSet(), asBag(), asSequence()
 */
public class OclCollectionConversion extends TermSymbol {

    private int collectionKind;
   
    public OclCollectionConversion(Name name, int collectionKind) {
	super(name, OclSort.COLLECTION_OF_OCLANY);
	this.collectionKind = collectionKind;
    }

    /** @return arity of the Function as int */
    public int arity() {
	return 1;
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

	OclSort elemSort = ((CollectionSort)subTerm[0].sort()).getElemSort();
	return CollectionSort.getCollectionSort(this.collectionKind, elemSort);
    }
  
    public String toString() {
	return (name()+":"+ OclSort.COLLECTION_OF_OCLANY);
    }
    
    public String proofToString() {
       String s = OclSort.COLLECTION_OF_OCLANY+" "+name();
       s+="(" + OclSort.COLLECTION_OF_OCLANY;
       s+=");\n";
       return s;
    }
}
