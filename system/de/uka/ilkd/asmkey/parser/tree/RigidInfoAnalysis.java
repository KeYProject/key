// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.tree;

import de.uka.ilkd.asmkey.logic.DerivedFunction;
import de.uka.ilkd.asmkey.logic.ParsingDerivedFunction;
import de.uka.ilkd.asmkey.util.graph.Stabilization;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.NonRigid;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * This class computes wether a derived function is "dynamic" or
 * not. It uses the {@link Stabilization} because there is recursive
 * functions.
 */
public class RigidInfoAnalysis extends Stabilization {
    
    private DerivedGraph graph;

    public RigidInfoAnalysis(DerivedGraph graph) {
	super(graph.graph());
	this.graph = graph;
    }

    protected void doVertexWork(Named name) {
	DerivedFunction func = graph.get(name.name());
	if (func instanceof ParsingDerivedFunction) {
	    computeInfo(func.body(), (ParsingDerivedFunction)func);
	}
    }

    private void computeInfo(Term term, ParsingDerivedFunction func) {
	if (func.isRigid()) {
	    Operator op = term.op();
	    if (op instanceof NonRigid) {
		func.setNonRigid();
		noFixPoint();
		return;
	    } else if (op instanceof ParsingDerivedFunction) {
		ParsingDerivedFunction tmp = (ParsingDerivedFunction) op;
		if (!tmp.isRigid()) {
		    func.setNonRigid();
		    noFixPoint();
		    return;
		}
	    }
	    for(int i=0; i<term.arity(); i++) {
		computeInfo(term.sub(i), func);
	    }
	}
    }

}
