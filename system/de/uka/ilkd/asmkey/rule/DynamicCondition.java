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
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/** Taclet condition for terms with dynamic top level operator
 * (function symbol).
 *
 * @see StaticCondition
 * @see PureCondition
 * @author Hubert Schmid
 */

public final class DynamicCondition extends VariableConditionAdapter {

    /** the instantiation of this schema variable is checked on taclet
     * application. */
    private final SchemaVariable v;


    /** create a condition for the given schema variable. */
    public DynamicCondition(SchemaVariable v) {
        this.v = v;
    }


    /** Check if the term has a dynamic top level operator (function
     * symbol). */
    public boolean check(SchemaVariable var, SVSubstitute instCandidate, 
			 SVInstantiations svInst, Services services) {
        /* Only check, if the schema variable matches. Else this
         * method is called later. */
        if (var == v) {
            return ((Term)instCandidate).op() instanceof NonRigidFunction;
        } else {
            return true;
        }
    }

}
