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


import de.uka.ilkd.asmkey.logic.AsmUtil;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/** Taclet condition for terms with static (rigid) arguments. A term
 * is static if it doesn't contain modal operators or dynamic function
 * symbols.
 *
 * @see AsmUtil#isStatic
 * @author Hubert Schmid
 */

public final class StaticArgsCondition extends VariableConditionAdapter {

    /** The instantiation ofthis schema variable is checked. */
    private final SchemaVariable v;


    /** Create a 'static argument condition' for the given schema
     * variable. */
    public StaticArgsCondition(SchemaVariable v) {
        this.v = v;
    }


    /** Check if all subterms of the given term are static. */
    public boolean check(SchemaVariable var, SVSubstitute subst, 
			 SVInstantiations svInst, Services services) {
        /* Only check, if the schema variable matches. Else this
         * method is called later. */
	Term term = (Term) subst;
        if (var == v) {
            for (int i = 0; i < term.arity(); ++i) {
                if (!AsmUtil.isStatic(term.sub(i))) {
                    return false;
                }
            }
            return true;
        } else {
            /* check in a later invocation of this method. */
            return true;
        }
    }

}
