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
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.oclsort.CollectionSort;
import de.uka.ilkd.key.logic.sort.oclsort.OclAnySort;
import de.uka.ilkd.key.logic.sort.oclsort.OclSort;

/**
 * Represents the OCL operation: collect()
 */
public class OclCollect extends OclCollOpBound {
       
    public OclCollect() {
	super(new Name("$collect"), OclSort.OCLANY, OclSort.COLLECTION_OF_OCLANY);
    }

    public Sort sort(Term[] subTerm) {
	Sort resultSort = null;
	CollectionSort collSort = (CollectionSort)subTerm[0].sort();
	OclAnySort exprSort = (OclAnySort)subTerm[1].sort();
	if (collSort.getCollectionKind() == CollectionSort.SET
	    || collSort.getCollectionKind() == CollectionSort.BAG) {
	    resultSort = CollectionSort.getCollectionSort(CollectionSort.BAG, 
							  exprSort);
	} else {
	    resultSort = CollectionSort.getCollectionSort(CollectionSort.SEQUENCE, 
							  exprSort);
	}
	return resultSort;
    }
  
    public String toString() {
	return (name()+":"+OclSort.BAG_OF_OCLANY);
    }
    
    public String proofToString() {
       String s = OclSort.BAG_OF_OCLANY+" "+name();
       s+="(" + OclSort.COLLECTION_OF_OCLANY + "," + OclSort.OCLANY;
       s+=");\n";
       return s;
    }
}
