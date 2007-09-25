// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.rule;


import de.uka.ilkd.asmkey.logic.AsmJunctor;
import de.uka.ilkd.asmkey.logic.AsmOperator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** Taclet condition for formulas. check if a formula
 *  is atomic.
 *
 * @author Stanislas Nanchen
 * @author Hubert Schmid
 */

public class AtomicCondition extends VariableConditionAdapter {

    /** The instantiation of this schema variable is checked. */
    private final SchemaVariable v;

    /** Create a 'pure condition' for the given schema variable. */
    public AtomicCondition(SchemaVariable v) {
        this.v = v;
    }

    /** Check if it is a atomic formula */
    public boolean check(SchemaVariable var, SVSubstitute sub, SVInstantiations svInst, Services javaServices) {
	/* Only check, if the schema variable matches. Else this
         * method is called later. BAD : TO CHANGE */
        if (sub instanceof Term) {
	    if (var == v) {
		Term term = (Term) sub;
		if (term.op() instanceof Junctor ||
		    term.op() instanceof AsmOperator ||
		    term.op() instanceof AsmJunctor) {
		    return false;
		} else {
		    return true;
		}
	    } else {
		return true;
	    }
	}
	else {
	    return true;
	}
    }

    /** Check if it is a atomic formula */
    public boolean check(SchemaVariable var, SVSubstitute term, SVInstantiations svInst) {
	return check(var, term, svInst, null);
    }

}
