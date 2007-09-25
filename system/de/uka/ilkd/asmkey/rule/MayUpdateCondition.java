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
import de.uka.ilkd.asmkey.logic.UpdateDFInfoContainer;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** This condition check if a rule #R may update a function dynamic
 * function; this is determined by static analysis.
 * @author Stanislas Nanchen
 */
public final class MayUpdateCondition extends AbstractTwoSchemaVariablesCondition {

    public MayUpdateCondition(boolean may, SchemaVariable r, SchemaVariable t) {
	super(may, r, t);
    }

    /** Check the condition. */
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
                return (AsmUtil.mayUpdate((UpdateDFInfoContainer) term, ty)) == equal;
            }
        } else if (var == y) {
            Term tx = getInstantiation(svInst, x);
            if (tx == null) {
                /* The condition can only be checked, if both
                 * variables are instantiated. */
                return true;
            } else {
                return (AsmUtil.mayUpdate((UpdateDFInfoContainer) tx, term)) == equal;
            }
        } else {
            return true;
        }
	
    }
}
