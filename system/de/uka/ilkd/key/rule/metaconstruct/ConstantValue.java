// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Replace a program variable that is a compile-time constant with the
 * value of the initializer
 */
public class ConstantValue extends AbstractMetaOperator {


    public ConstantValue() {
	super(new Name("#constantvalue"), 1);
    }


    /**
     * checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the @link Term is valid.
     */
    public boolean validTopLevel(Term term) {
	// a meta operator accepts almost everything
	return  term.arity()==arity();
    }

    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
	term = term.sub ( 0 );
	Operator op = term.op ();

	if ( op instanceof ProgramConstant ) {
	    Literal lit = ((ProgramConstant)op).getCompileTimeConstant ();
	    if ( lit != null )
		term = services.getTypeConverter ()
		    .convertToLogicElement ( lit );
	}

	return term;
    }

}
