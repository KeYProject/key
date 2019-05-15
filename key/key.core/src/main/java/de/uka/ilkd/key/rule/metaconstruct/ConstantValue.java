// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Replace a program variable that is a compile-time constant with the
 * value of the initializer
 */
public final class ConstantValue extends AbstractTermTransformer {


    public ConstantValue() {
	super(new Name("#constantvalue"), 1);
    }


    public Term transform(Term term, SVInstantiations svInst, Services services) {
	term = term.sub ( 0 );
	Operator op = term.op ();

	if(op instanceof ProgramConstant) {
	    Literal lit = ((ProgramConstant)op).getCompileTimeConstant();
	    if(lit != null) {
		term = services.getTypeConverter().convertToLogicElement(lit);
	    }
	}

	return term;
    }
}