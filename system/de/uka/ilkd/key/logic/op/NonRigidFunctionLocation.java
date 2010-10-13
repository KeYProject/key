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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;


public class NonRigidFunctionLocation extends Function implements NonRigid, Location {

    /** boolean function indicating if the location shall be considered as part 
     * of the heap. If true heap dependent function symbols may deend on this location 
     */
    private final boolean isHeap;

    /**
     * creates a non rigid function location with given signature
     * @param name the Name of the non-rigid function symbol
     * @param sort the Sort of the symbol
     * @param argSorts the array of Sort defining the argument sorts
     * @param isHeap boolean indicating if the location shall be considered 
     * as part of the heap 
     */
    public NonRigidFunctionLocation(Name name, Sort sort, Sort[] argSorts, boolean isHeap) {
        super(name, sort, argSorts);
        this.isHeap = isHeap;
    }

    /**
     * creates a non rigid function location  with given signature
     * @param name the Name of the non-rigid function symbol
     * @param sort the Sort of the symbol
     * @param argSorts the ArrayOf<Sort> defining the argument sorts
     * @param isHeap boolean indicating if the location shall be considered 
     * as part of the heap 
     */
    public NonRigidFunctionLocation(Name name, Sort sort, ImmutableArray<Sort> argSorts, boolean isHeap) {
        super(name, sort, argSorts);
        this.isHeap = isHeap;
    }
    
    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid (Term term) {
	return false;
    }

    public boolean mayBeAliasedBy(Location loc){
	return (this==loc);
    }
    
    
    public String proofToString() {
        return isHeap ? "\\nonRigid[Location] " + super.proofToString() :
            "\\nonRigid[LocationNoHeap] " + super.proofToString();
    }

    /**
     * signals if the location function should be considered as part of the heap
     * this implies that heap dependant funtion may depend on it
     * @return if this location shall be considered as part of he heap
     */
    public boolean isHeap() {
	return isHeap;
    }
}
