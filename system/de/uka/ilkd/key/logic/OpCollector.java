// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.*;

import java.util.HashSet;

/**
 * Collects all operators occuring in the traversed term.
 */

public class OpCollector extends Visitor{
    /** the found operators */
    private HashSet ops;

    /** creates the Op collector */
    public OpCollector() {
	ops = new HashSet();
    }

    public void visit(Term t) {	
        ops.add(t.op());
    }

    public boolean contains(Operator op) {
	return ops.contains(op);
    }

}
