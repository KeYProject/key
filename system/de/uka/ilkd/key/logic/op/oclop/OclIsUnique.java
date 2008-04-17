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
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.oclsort.OclSort;

/**
 * Represents the OCL operation: isUnique()
 */
public class OclIsUnique extends OclCollOpBound {
       
    public OclIsUnique() {
	super(new Name("$isUnique"), OclSort.OCLANY, OclSort.BOOLEAN);
    }

    public Sort sort(Term[] subTerm) {
	helpSort(subTerm);
	return OclSort.BOOLEAN;
    }
  
    public String toString() {
	return (name()+":"+OclSort.BOOLEAN);
    }
    
    public String proofToString() {
       String s = OclSort.BOOLEAN+" "+name();
       s+="(" + OclSort.COLLECTION_OF_OCLANY + "," + OclSort.OCLANY;
       s+=");\n";
       return s;
    }
}
