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
 * Super class for all OCL operators that handles one
 * iteration variable: any(), collect(), exists(), forAll(),
 * isUnique(), one(), reject(), select(), sortedBy()
 */
public abstract class OclCollOpBound extends TermSymbol {

    private Sort expressionSort;
       
    public OclCollOpBound(Name name, Sort expressionSort, Sort resultSort) {
	super(name, resultSort);
	this.expressionSort = expressionSort;
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
	    || term.varsBoundHere(1).size()!=1) {
	    return false; 
	}
	if (!(term.sub(0).sort() instanceof CollectionSort)) {
	    return false;
	}
	CollectionSort collSort = (CollectionSort)term.sub(0).sort();
	Sort iterVariableSort = term.varsBoundHere(1).get(0).sort();
	Sort exprSort = term.sub(1).sort();
	if (!collSort.getElemSort().extendsTrans(iterVariableSort)) {
	    return false;
	}
        return exprSort.extendsTrans(this.expressionSort);
    }

    public void helpSort(Term[] subTerm) {
	if (subTerm.length != arity()) {
	    throw new IllegalArgumentException("Cannot determine sort of "+
						"invalid term (Wrong arity).");
	}
	if (!(subTerm[0].sort() instanceof CollectionSort)) {
	    throw new IllegalArgumentException("Cannot determine sort of "+
						"invalid term (First argument must be a Collection).");
	}
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
