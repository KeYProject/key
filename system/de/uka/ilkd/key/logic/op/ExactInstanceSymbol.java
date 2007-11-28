// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on 15.03.2005
 */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * "S::ExactInstanceof" is a function symbol parameterised with sort <code>S</code>
 * testing if a given argument has sort <code>S</code> as
 * exact type (dynamic type)
 */
public class ExactInstanceSymbol extends SortDependingFunction {
  
    public static final Name NAME=new Name("exactInstance");

    public ExactInstanceSymbol ( Sort p_sort, Sort booleanSort) {
	super ( new Name ( "" + p_sort.name () + "::" + NAME ),
		booleanSort,
		new Sort [] { Sort.ANY },
		NAME,
		p_sort );
    }

    /**
     * This operator can be used with arbitrary arguments 
     * (only mixing primitive and reference sorts is not allowed)
     */
    public boolean possibleSub(int at, Term possibleSub) {
	if (possibleSub.op() instanceof SchemaVariable) {
	    return true;
	}
	return 
            (possibleSub.sort() instanceof PrimitiveSort) == 
                (getSortDependingOn() instanceof PrimitiveSort);
	 
    }
}
