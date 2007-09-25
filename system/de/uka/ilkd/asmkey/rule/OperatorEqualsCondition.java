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


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/** Taclet condition that checks if two terms have the same top level
 * operator.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */

public final class OperatorEqualsCondition extends AbstractTwoSchemaVariablesCondition {


    /** Creates condition for the given schema variables. If 'equal ==
     * true', the operators must match, else the operators must
     * differ. */
    public OperatorEqualsCondition(boolean equal, SchemaVariable x, SchemaVariable y) {
        super(equal, x, y);
    }


    /** Check if the instantiations for schema variables x and y have
     * the same top level operator. */
    public boolean check(SchemaVariable var, SVSubstitute subst, 
			 SVInstantiations svInst, Services services) {
	Term term = (Term) subst;
        /* This method is called each time a schema variable is
         * instantiated. We have to check, if the schema variable
         * matches 'x' or 'y' and the other schema variable is already
         * instantiated. Else we return 'true' and check the condition
         * on a later invocation of this method. */
        if (var == x) {
            Term ty = getInstantiation(svInst, y);
            if (ty == null) {
                /* The condition can only be checked, if both
                 * variables are instantiated. */
                return true;
            } else {
                return (term.op() == ty.op()) == equal;
            }
        } else if (var == y) {
            Term tx = getInstantiation(svInst, x);
            if (tx == null) {
                /* The condition can only be checked, if both
                 * variables are instantiated. */
                return true;
            } else {
                return (term.op() == tx.op()) == equal;
            }
        } else {
            return true;
        }
    }

}
