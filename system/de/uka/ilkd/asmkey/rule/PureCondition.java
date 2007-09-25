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


/** Taclet condition for pure terms. A term is pure if it doesn't
 * contain any modal operators.
 *
 * @see AsmUtil#isPure
 * @see DynamicCondition
 * @see StaticCondition
 * @author Hubert Schmid
 */

public final class PureCondition extends VariableConditionAdapter {

    /** The instantiation of this schema variable is checked. */
    private final SchemaVariable v;


    /** Create a 'pure condition' for the given schema variable. */
    public PureCondition(SchemaVariable v) {
        this.v = v;
    }


    /** Check if the term is pure. */
    public boolean check(SchemaVariable var, SVSubstitute instCandidate, 
			 SVInstantiations svInst, Services services) {
        /* Only check, if the schema variable matches. Else this
         * method is called later. */
        if (var == v) {
            return AsmUtil.isPure((Term)instCandidate);
        } else {
            return true;
        }
    }

}
