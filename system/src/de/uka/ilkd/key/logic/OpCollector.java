// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.logic;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * Collects all operators occurring in the traversed term.
 */
public class OpCollector extends DefaultVisitor {
    /** the found operators */
    private HashSet<Operator> ops;

    /** creates the Op collector */
    public OpCollector() {
	ops = new LinkedHashSet<Operator>();
    }

    public void visit(Term t) {	
        ops.add(t.op());
        if(t.op() instanceof ElementaryUpdate) {
            ops.add(((ElementaryUpdate)t.op()).lhs());
        }
    }

    public boolean contains(Operator op) {
	return ops.contains(op);
    }
    
    public Set<Operator> ops() {
	return ops;
    }
}
