// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/** 
 * A structure for storing the arguments to an Operator
 * when creating a Term. Each argument, in form of a Term,
 * can have bound variables, in form of an ArrayOf<QuantifiableVariable>.
 * This class allows efficient extraction of the different parts.  
 */
public class PairOfTermArrayAndBoundVarsArray {
    private Term[] term;
    private ImmutableArray<QuantifiableVariable>[] var;

    public PairOfTermArrayAndBoundVarsArray(List list) {
	term = new Term[list.size()];
	var = new ImmutableArray[list.size()];
	boolean hasBoundVars = false;
	Iterator iter = list.iterator();
	for (int i=0; iter.hasNext(); i++) {
	    TermWithBoundVars t = (TermWithBoundVars)iter.next();
	    term[i] = t.term;
	    if (t.boundVars == null) {
		var[i] = new ImmutableArray<QuantifiableVariable>
		    (new QuantifiableVariable[0]);
	    } else {
		var[i] = t.boundVars;
		hasBoundVars = true;
	    }
	}
	if (!hasBoundVars) {
	    var = null;
	}
    }

    public Term[] getTerms() {
	return term;
    }

    public ImmutableArray<QuantifiableVariable>[] getBoundVars() {
	return var;
    }

    public int size() {
	return term.length;
    }
    
}
