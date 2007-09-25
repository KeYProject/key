// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.decproc;
import de.uka.ilkd.key.logic.Term;

/**
 * A Wrapper class to export different .hashCode() and .equals(o) functions
 */
public class UninterpretedTermWrapper {
    private Term eps;

    public UninterpretedTermWrapper(Term term) {
	eps = term;
    }

    /**
     * Returns A hash code compatible with the equalsModRenaming function of eps.
     * For now this is a dummy value which forces HashSets to put all 
     * UninterpretedTermWrappers in the same slot so that the .equals(o) 
     * function has to be employed.
     * Later this linear effort should be replaced.
     * @returns A hash code compatible with the equalsModRenaming function of eps.
     */
    public int hashCode(){
	return 42;
    }

    /**
     * Returns true iff eps.equalsModRenaming(o).
     * @returns true iff eps.equalsModRenaming(o)
     * @param o The Object which eps should be compared with;
     *        if o is not a Term, then normal .equals is used.
     */
    public boolean equals(Object o){
	if (o instanceof Term)
	    return ((Term) eps).equalsModRenaming(o);
	else
	    return false;
    }

}
