// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.simplify.translation;

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
     * Compares using eps.equalsModRenaming().
     */
    @Override
    public boolean equals(Object o) {
	if (o instanceof UninterpretedTermWrapper)
	    return eps.equalsModRenaming(((UninterpretedTermWrapper) o).eps);
	else
	    return false;
    }

    /**
     * Returns A hash code compatible with the equalsModRenaming function of
     * eps. For now this is a dummy value which forces HashSets to put all
     * UninterpretedTermWrappers in the same slot so that the .equals(o)
     * function has to be employed. Later this linear effort should be replaced.
     * 
     * @returns A hash code compatible with the equalsModRenaming function of
     *          eps.
     */
    @Override
    public int hashCode() {
	return 42;
    }

}
