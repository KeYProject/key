// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.ArrayOfTerm;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;


/** 
 * Abstract sorted operator class offering some common functionality.
 */
public abstract class AbstractSortedOperator extends AbstractOperator 
                                             implements SortedOperator {
    
    private final Sort sort;
    private final ArrayOfSort argSorts;
   	
    
    protected AbstractSortedOperator(Name name,
	    			     ArrayOfSort argSorts,
	    		             Sort sort) {
	super(name, argSorts.size());
	this.argSorts = argSorts;	
	this.sort = sort;
    }
    
    
    protected AbstractSortedOperator(Name name, 
	    			     Sort[] argSorts, 
	    			     Sort sort) {
	this(name, new ArrayOfSort(argSorts), sort);
    }
    

    @Override
    public final Sort sort(ArrayOfTerm terms) {
	return sort;
    }
    
    
    /**
     * checks if a given Term could be subterm (at the at'th subterm
     * position) of a term with this function at its top level. The
     * validity of the given subterm is NOT checked.  
     * @param at theposition of the term where this method should check 
     * the validity.  
     * @param possibleSub the subterm to be ckecked.
     * @return true iff the given term can be subterm at the indicated
     * position
     */
    private boolean possibleSub(int at, Term possibleSub) {
	Sort sort = possibleSub.sort();
	
	if (possibleSub.op() instanceof SchemaVariable 
            || sort == AbstractMetaOperator.METASORT
	    || sort instanceof ProgramSVSort
	    || argSort(at) == AbstractMetaOperator.METASORT
	    || argSort(at) instanceof ProgramSVSort) {
	    return true;
	} else {
	    return sort.extendsTrans(argSort(at));
	}
    }
    
    
    protected boolean additionalValidTopLevel(Term term) {
	return true;
    }
    
    
    @Override
    public final boolean validTopLevel(Term term) {
	if(term.arity() != arity()) {
	    return false;
	}
	for(int i = 0, n = arity(); i < n; i++) {
            if(!possibleSub(i, term.sub(i))) { 
		return false;
	    }
	}
	return additionalValidTopLevel(term);
    }
    
    
    @Override    
    public final Sort argSort(int i) {
	return argSorts.getSort(i);
    }
    
    
    @Override
    public final ArrayOfSort argSorts() {
	return argSorts;
    }
    
    
    @Override
    public final Sort sort() {
	return sort;
    }
}
