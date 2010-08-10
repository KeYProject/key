// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.sort.oclsort.OclSort;

/**
 * Represents the OCL operation: sortedBy()
 */
public class OclSortedBy extends OclCollOpBound {
       
    public OclSortedBy() {
	super(new Name("$sortedBy"), OclSort.REAL, OclSort.SEQUENCE_OF_OCLANY);
    }

    public Sort sort(Term[] subTerm) {
	helpSort(subTerm);
	OclSort elemSort = ((CollectionSort)subTerm[0].sort()).getElemSort();
	return CollectionSort.getCollectionSort(CollectionSort.SEQUENCE, elemSort);
    }
  
    public String toString() {
	return (name()+":"+OclSort.SEQUENCE_OF_OCLANY);
    }
    
    public String proofToString() {
       String s = OclSort.SEQUENCE_OF_OCLANY+" "+name();
       s+="(" + OclSort.COLLECTION_OF_OCLANY + "," + OclSort.REAL;
       s+=");\n";
       return s;
    }
}
