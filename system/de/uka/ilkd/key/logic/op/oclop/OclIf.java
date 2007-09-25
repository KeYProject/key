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
 * Represents the OCL operation: if-then-else-endif
 */
public class OclIf extends TermSymbol {
       
    public OclIf() {
	super(new Name("$if"), null);
    }
    
    /** @return arity of the Function as int */
    public int arity() {
	return 3;
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
	if (term.sub(0).sort() != OclSort.BOOLEAN) {
	    return false;
	}
	if (!(term.sub(1).sort().extendsTrans(term.sub(2).sort()))
	    && !(term.sub(2).sort().extendsTrans(term.sub(1).sort()))) {
	    return false;
	}
        return true;
    }

    public Sort sort(Term[] subTerm) {
	if (subTerm.length != arity()) {
	    throw new IllegalArgumentException("Cannot determine sort of "+
						"invalid term (Wrong arity).");
	}
	if (subTerm[1].sort().extendsTrans(subTerm[2].sort())) {
	    return subTerm[2].sort();
	} else if (subTerm[2].sort().extendsTrans(subTerm[1].sort())) {
	    return subTerm[1].sort();
	} else {
	   throw new IllegalArgumentException("Cannot determine sort of "+
						"invalid term (Arguments must have a common supersort)."); 
	}
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
