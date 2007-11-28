// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.sort.oclsort;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.*;

public class OclAnySort implements OclSort {
    
    private Name name;

    public OclAnySort(Name name) {
	this.name = name;
    }

    /** @return name of the Sort */
    public Name name() {
	return name;
    }
    
    /**
     * For finding out whether a certain sort is super- or subsort of another
     * sort or not, please use <code>extendsTrans</code>. 
     * Using <code>extendsSorts()</code> for this purpose may lead to 
     * undesired results when dealing with arraysorts! 
     * @return the sorts of the predecessors of this sort
     */
    public SetOfSort extendsSorts() {
	return SetAsListOfSort.EMPTY_SET;
    }

    /**
     * returns true iff the given sort is a transitive supersort of this sort
     * or it is the same.
     */
    public boolean extendsTrans(Sort s) {
	if (s instanceof OclGenericSort) {
	    return true;
	} else if (s instanceof GenericSort) {
	    if (((GenericSort)s).getOneOf().size() == 0) {
		return true;
	    } else {
		IteratorOfSort iter = ((GenericSort)s).getOneOf().iterator();
		while (iter.hasNext()) {
		    if (this.extendsTrans(iter.next())) {
			return true;
		    }
		}
		return false;
	    }
	} else {
	    return s.getClass().isInstance(this);
	}
    }

    /** @return equality symbol of this sort */
    public Equality getEqualitySymbol() {
	return Op.EQUALS;
    }
    
    public String toString() {
	return name.toString();
    }
}
