// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Op;

public class NullSortImpl extends ClassInstanceSortImpl implements NullSort {

    /** creates a NullSort*/
    public NullSortImpl(Name name) {
	super(name, false);
    }

    /**
     * returns true iff the given sort is an object sort
     */
    public boolean extendsTrans(Sort s) {
       return s==Sort.ANY || (s instanceof ObjectSort);
    }

    /** @return equality symbol of this sort */
    public Equality getEqualitySymbol(){
	return Op.EQUALS;
    }

    /**
     * @return an object of this class with elementSort().equals(p),
     * or null if such an object cannot be constructed (as p is an
     * incompatible sort)
     */
    public Sort cloneFor ( Sort p ) {
	return this;
    }
}
