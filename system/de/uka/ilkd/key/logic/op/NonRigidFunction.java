// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
/*
 * Created on 18.01.2005
 */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Non-rigid function or predicate symbols are realised as instances
 * of this class. Some particular non-rigid functions 
 * (namely attributes and arrays) are currently bypassing this class,
 * but should be integrated into this framework in the mid-future (this
 * was written 2005, may be you read this in the year 2035;-).
 */
public class NonRigidFunction extends Function implements NonRigid {

    /**
     * creates a non rigid function with given signature
     * @param name the Name of the non-rigid function symbol
     * @param sort the Sort of the symbol
     * @param argSorts the array of Sort defining the argument sorts
     */
    public NonRigidFunction(Name name, Sort sort, Sort[] argSorts) {
        super(name, sort, argSorts);       
    }

    /**
     * creates a non rigid function with given signature
     * @param name the Name of the non-rigid function symbol
     * @param sort the Sort of the symbol
     * @param argSorts the ArrayOf<Sort> defining the argument sorts
     */
    public NonRigidFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
        super(name, sort, argSorts);      
    }
    
    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid (Term term) {
	return false;
    }
    
    
    public String proofToString() {
        return "\\nonRigid " + super.proofToString(); 
    }
}
