/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;



public final class DifferentInstantiationCondition extends VariableConditionAdapter {

    private final SchemaVariable var1, var2;

    public DifferentInstantiationCondition(SchemaVariable var1, SchemaVariable var2) {
        this.var1 = var1;
        this.var2 = var2;
    }


    @Override
    public boolean check(SchemaVariable var, SVSubstitute candidate, SVInstantiations svInst,
            Services services) {
        if (var == var1) {
            final Object inst2 = svInst.getInstantiation(var2);
            return inst2 == null || !inst2.equals(candidate);
        } else if (var == var2) {
            final Object inst1 = svInst.getInstantiation(var1);
            return inst1 == null || !inst1.equals(candidate);
        } else {
            return true;
        }
    }


    @Override
    public String toString() {
        return "\\different (" + var1 + ", " + var2 + ")";
    }
}
