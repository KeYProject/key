// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.SortDependingSymbol;

public abstract class AbstractNonCollectionSort extends AbstractSort implements
        NonCollectionSort {

    protected final AbstractCollectionSort setSort;

    protected final AbstractCollectionSort bagSort;

    protected final AbstractCollectionSort sequenceSort;
  

    /** creates a Sort (with a new equality symbol for this sort) */
    public AbstractNonCollectionSort(Name name) {
        super(name);
        setSort      = new SetSort(this);
        bagSort      = new BagSort(this);
        sequenceSort = new SequenceSort(this);
    }

    public CollectionSort getSetSort() {
        return setSort;
    }

    public CollectionSort getBagSort() {
        return bagSort;
    }

    public CollectionSort getSequenceSort() {
        return sequenceSort;
    }    
    
    public SortDependingSymbol lookupSymbol(Name p_name) {
	SortDependingSymbol result = super.lookupSymbol(p_name);
	if(result == null) {
	    result = setSort.lookupSymbol(p_name);
	}
	if(result == null) {
	    result = bagSort.lookupSymbol(p_name);
	}
	if(result == null) {
	    result = sequenceSort.lookupSymbol(p_name);
	}
	return result;
    }
    
    public void addDefinedSymbols(Namespace functions, Namespace sorts) {
	super.addDefinedSymbols(functions, sorts);
	setSort.addDefinedSymbols(functions, sorts);
	bagSort.addDefinedSymbols(functions, sorts);
	sequenceSort.addDefinedSymbols(functions, sorts);
    }
}
