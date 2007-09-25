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


/** Taclet condition for static (rigid) terms. A term is static if it
 * doesn't contain modal operators and dynamic funciton symbols.
 *
 * @see AsmUtil#isStatic
 * @see DynamicCondition
 * @see PureCondition
 * @author Hubert Schmid
 */

public final class StaticCondition extends VariableConditionAdapter {

    /** The instantiation of this schema variable is checked. */
    private final SchemaVariable v;


    /** Create a 'static condition' for the given schema variable. */
    public StaticCondition(SchemaVariable v) {
        this.v = v;
    }


    /** Check if the term is static. */
    public boolean check(SchemaVariable var, SVSubstitute instCandidate, 
			 SVInstantiations svInst, Services services) {
        /* Only check, if the schema variable matches. Else this
         * method is called later. */
        if (var == v) {
            return AsmUtil.isStatic((Term)instCandidate);
        } else {
            return true;
        }
    }

}
