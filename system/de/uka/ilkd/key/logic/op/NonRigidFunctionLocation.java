// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;


public class NonRigidFunctionLocation extends Function implements NonRigid, Location {

    /**
     * creates a non rigid function location with given signature
     * @param name the Name of the non-rigid function symbol
     * @param sort the Sort of the symbol
     * @param argSorts the array of Sort defining the argument sorts
     */
    public NonRigidFunctionLocation(Name name, Sort sort, Sort[] argSorts) {
        super(name, sort, argSorts);       
    }

    /**
     * creates a non rigid function location  with given signature
     * @param name the Name of the non-rigid function symbol
     * @param sort the Sort of the symbol
     * @param argSorts the ArrayOfSort defining the argument sorts
     */
    public NonRigidFunctionLocation(Name name, Sort sort, ArrayOfSort argSorts) {
        super(name, sort, argSorts);      
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
        return "\\nonRigid[Location] " + super.proofToString();
    }
}
