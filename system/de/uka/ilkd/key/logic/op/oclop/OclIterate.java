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
 * Represents the OCL operation: iterate()
 */
public class OclIterate extends TermSymbol {
       
    public OclIterate() {
	super(new Name("$iterate"), null);
    }
    
    /** @return arity of the Function as int */
    public int arity() {
	return 3;
    }

    /**
     * checks if the given term is syntactically valid at its top
     * level assumed the top level operator were this, i.e. if the
     * direct subterms can be subterms of a term with this top level
     * operator, the method returns true. Furthermore, it is checked
     * that no variables are bound for none of the subterms.  
     * @param term the Term to be checked.  
     * @return true iff the given term has
     * subterms that are suitable for this function.
     */
    public boolean validTopLevel(Term term){
	if (term.arity()!=arity()) {
	    return false;
	}
	if (term.varsBoundHere(0).size()!=0
	    || term.varsBoundHere(1).size()!=0
	    || term.varsBoundHere(2).size()!=2) {
	    return false; 
	}
	if (!(term.sub(0).sort() instanceof CollectionSort)) {
	    return false;
	}
	CollectionSort collSort = (CollectionSort)term.sub(0).sort();
	Sort iterVariableSort = term.varsBoundHere(2).get(0).sort();
	Sort accVariableSort = term.varsBoundHere(2).get(1).sort();
	Sort initAccValueSort = term.sub(1).sort();
	Sort exprSort = term.sub(2).sort();
	if (!collSort.getElemSort().extendsTrans(iterVariableSort)) {
	    return false;
	}
	if (!initAccValueSort.extendsTrans(accVariableSort)) {
	    return false;
	}
	if (!exprSort.extendsTrans(accVariableSort)) {
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
	return subTerm[2].sort();
    } 
  
    public String toString() {
	return (name() + ":"+OclSort.OCLGENERIC);
    }
    
    public String proofToString() {
       String s = OclSort.OCLGENERIC+" "+name();
       s+="(" + OclSort.COLLECTION_OF_OCLANY + ","
	   +OclSort.OCLGENERIC+","+OclSort.OCLGENERIC;
       s+=");\n";
       return s;
    }
}
