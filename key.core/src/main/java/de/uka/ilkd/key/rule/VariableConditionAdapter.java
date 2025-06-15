/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

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
    public abstract boolean check(SchemaVariable var, SyntaxElement instCandidate,
            SVInstantiations instMap, Services services);



    public final MatchResultInfo check(SchemaVariable var,
            SyntaxElement instCandidate,
            MatchResultInfo mc, LogicServices services) {
        return check(var, instCandidate, (SVInstantiations) mc.getInstantiations(),
            (Services) services) ? mc : null;
    }
}
