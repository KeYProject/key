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

import de.uka.ilkd.asmkey.logic.DerivedFunction;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/** Taclet condition for terms. The conditions checks, if the top
 * level operator is an derived symbol call.
 *
 * @author Stanislas Nanchen
 * @author Hubert Schmid
 */

public final class DerivedCondition extends VariableConditionAdapter {

    /** the instantiation of this schema variable is checked. */
    private final SchemaVariable v;


    /** create a call condition for the given schema variable. */
    public DerivedCondition(SchemaVariable v) {
        this.v = v;
    }


    /** Check if the top level operator of the term is a invocation of
     * a named asm rule. */
    public boolean check(SchemaVariable var, 
			 SVSubstitute subst, 
			 SVInstantiations svInst,
			 Services services) {
	Term term = (Term) subst;
        /* Only check, if the schema variable matches. Else this
         * method is called later. */
        if (var == v) {
            return term.op() instanceof DerivedFunction;
        } else {
            return true;
        }
    }

}
