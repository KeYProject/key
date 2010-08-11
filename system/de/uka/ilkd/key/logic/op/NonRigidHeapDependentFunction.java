// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Instances of this classes represent non-rigid functions, which dependent only on the
 * state of the heap and not of any local variables. This means their interpretation coincides
 * on all states that describe the same heap. 
 * 
 * A famous representant of this kind of function is the <tt>inReachableState</tt> predicate.
 */
public class NonRigidHeapDependentFunction extends NonRigidFunction {

    /**
     * creates a non rigid function with given signature
     * @param name the Name of the non-rigid function symbol
     * @param sort the Sort of the symbol
     * @param argSorts the array of Sort defining the argument sorts
     */
    public NonRigidHeapDependentFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
        super(name, sort, argSorts);     
    }

    /**
     * creates a non rigid function with given signature
     * @param name the Name of the non-rigid function symbol
     * @param sort the Sort of the symbol
     * @param argSorts the array of Sort defining the argument sorts
     */
    public NonRigidHeapDependentFunction(Name name, Sort sort, Sort[] argSorts) {
        super(name, sort, argSorts);      
    }
    
    public String proofToString() {
        return "\\nonRigid[HeapDependent] " 
                + super.proofToString().substring("\\nonRigid ".length());
    }
}
