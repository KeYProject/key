/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;


/**
 * disjoin two variable conditions
 *
 * @author bruns
 */
public final class AlternativeVariableCondition extends VariableConditionAdapter {

    private final VariableConditionAdapter delegate0, delegate1;

    public AlternativeVariableCondition(VariableConditionAdapter delegate0,
            VariableConditionAdapter delegate1) {
        this.delegate0 = delegate0;
        this.delegate1 = delegate1;
    }

    /**
     * check whether any of the two delegates apply
     */
    @Override
    public boolean check(SchemaVariable var, SyntaxElement subst, SVInstantiations svInst,
            Services services) {
        return delegate0.check(var, subst, svInst, services)
                || delegate1.check(var, subst, svInst, services);

    }


    @Override
    public String toString() {
        return "\\or(" + delegate0 + "," + delegate1 + ")";
    }
}
