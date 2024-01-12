/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * The variable condition adapter can be used by variable conditions which can either fail or be
 * successful, but which do not create a constraint.
 */
public abstract class VariableConditionAdapter implements VariableCondition {

    /**
     * checks if the condition for a correct instantiation is fulfilled
     *
     * @param var the template Variable to be instantiated
     * @param instMap the MatchCondition with the current matching state and in particular the
     *        SVInstantiations that are already known to be needed
     * @param services the program information object
     * @return true iff condition is fulfilled
     */
    public abstract boolean check(SchemaVariable var, SVSubstitute instCandidate,
            SVInstantiations instMap, Services services);



    @Override
    public final MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions mc, Services services) {
        return check(var, instCandidate, mc.getInstantiations(), services) ? mc : null;
    }
}
