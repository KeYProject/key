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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Objects of this class represent the (logical) instanceof-operator;
 * for each object sort such an operator exists
 */
public class InstanceofSymbol extends SortDependingFunction {

    public static final Name NAME=new Name("instance");

    public InstanceofSymbol ( Sort p_sort, Sort booleanSort) {
	super ( new Name ( "" + p_sort.name () + "::" + NAME ),
		booleanSort,
		new Sort [] { Sort.ANY },
		NAME,
		p_sort );
    }

    public InstanceofSymbol ( Name name, Sort p_sort ) {
	super ( new Name ( "" + p_sort.name () + "::" + name),
		Sort.FORMULA,
		new Sort [] { Sort.ANY },
		name,
		p_sort );
    }


    /**
     * only type tests mixing primitive and reference types are omitted
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
