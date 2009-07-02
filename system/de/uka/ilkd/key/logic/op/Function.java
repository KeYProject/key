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
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;

public abstract class Function extends TermSymbol {
    
    /** 
     * sorts of arguments
     */
    private ArrayOfSort argSorts;
    
    /** creates a Function 
     * @param name String with name of the function
     * @param sort the Sort of the function (result type)
     * @param argSorts an array of Sort with the sorts of 
     * the function's arguments  
     */   
    public Function(Name name, Sort sort, Sort[] argSorts) {
	this(name, sort, new ArrayOfSort(argSorts));
    }


    /** creates a Function 
     * @param name String with name of the function
     * @param sort the Sort of the function (result type)
     * @param argSorts ArrayOfSort of the function's arguments
     */   
    public Function(Name name, Sort sort, ArrayOfSort argSorts) {
	super(name, argSorts.size(), sort);
	this.argSorts = argSorts;
    }

    /** @return array of allowed sorts of the function arguments */
    public ArrayOfSort argSort() {
	return argSorts;
    }

    /** @return Sort of the n-th argument */
    public Sort argSort(int n) {
	return argSorts.getSort(n);
    }

    /**
     * checks if a given Term could be subterm (at the atth subterm
     * position) of a term with this function at its top level. The
     * validity of the given subterm is NOT checked.  
     * @param at theposition of the term where this method should check 
     * the validity.  
     * @param possibleSub the subterm to be ckecked.
     * @return true iff the given term can be subterm at the indicated
     * position
     */
    public boolean possibleSub(int at, Term possibleSub) {
	if (possibleSub.op() instanceof SchemaVariable ||
	    possibleSub.sort() instanceof ProgramSVSort ||
	    possibleSub.op() instanceof MetaOperator) {
	    return true;
	}
	return possibleSub.sort().extendsTrans(argSort(at));
    }

    /**
     * checks if given Terms could be subterms of a term with this
     * function at its top level. The check includes the comparison of
     * the required number of subterms and the number of given
     * terms. The validity of the given subterms is NOT checked.
     * @param possibleSubs the subterms to be ckecked.  
     * @return true iff the given terms can be subterms and the number of given
     * terms and the required number of subterms are equal.
     */
    public boolean possibleSubs(Term[] possibleSubs ){
	if (possibleSubs.length!=arity()) return false;
        for (int i=0; i<arity(); i++) {
	    if (!possibleSub(i,possibleSubs[i])) {
		return false;
	    }
	}
        return true;
    }

    /**
     * checks if the given term is syntactically valid at its top
     * level assumed the top level operator were this, i.e. if the
     * direct subterms can be subterms of a term with this top level
     * operator, the method returns true. Furthermore, it is checked
     * that no variables are bound for none of the subterms.  
     * @param term the Term to be checked.
     * @return true iff the given term has subterms that are suitable
     * for this function.
     */
    public boolean validTopLevel(Term term){
	if (term.arity()!=arity()) {
	    return false;
	}
	for (int i=0; i<arity(); i++) {
            if (!possibleSub(i,term.sub(i))) { 
		return false;
	    }
	    //Need to comment this away because of OCL simplification
	    //BinaryBindingTerm & TernaryBindingTerm have
	    //"Function" as operator and have bound vars
	    //if (term.varsBoundHere(i).size()!=0) {
	    //	return false; 
	    //}
	}
        return true;
    }

  
    public String toString() {
	return (name()+((sort()==Sort.FORMULA)? "" : ":"+sort()));
    }
    
    public String proofToString() {
       String s = null;
       if (sort() != null) {
	   s = (sort() == Sort.FORMULA ? "" : sort().toString()) + " ";
	   s += name();
       } else {
	   s = "NO_SORT"+" "+name();
       }
       if (arity()>0) {
          int i = 0;
          s+="(";
          while (i<arity()) {
             if (i>0) s+=",";
             s+=argSort(i);
             i++;
          }
          s+=")";
       }
       s+=";\n";
       return s;
    }

}
