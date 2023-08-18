/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * This variable condition checks if given two terms s, t both terms have a different unique symbol
 * as top level operator
 */
public final class DifferentFields extends VariableConditionAdapter {

    private final SchemaVariable var1, var2;

    public DifferentFields(SchemaVariable var1, SchemaVariable var2) {
        this.var1 = var1;
        this.var2 = var2;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate, SVInstantiations instMap,
            Services services) {

        if (var == var1) {
            final Object inst2 = instMap.getInstantiation(var2);
            return inst2 == null || checkHelp(instCandidate, inst2);
        } else if (var == var2) {
            final Object inst1 = instMap.getInstantiation(var1);
            return inst1 == null || checkHelp(inst1, instCandidate);
        } else {
            return true;
        }
    }

    public boolean checkHelp(Object o1, Object o2) {
        if (o1 instanceof Term && o2 instanceof Term) {
            final Term t1 = (Term) o1;
            final Term t2 = (Term) o2;

            if (t1.op() == t2.op()) {
                return false;
            } else if (t1.op() instanceof Function && t2.op() instanceof Function) {
                final Function op1 = (Function) t1.op();
                final Function op2 = (Function) t2.op();

                return op1.isUnique() && op2.isUnique();
            }
        }
        return false;
    }


    @Override
    public String toString() {
        return "\\differentFields (" + var1 + ", " + var2 + ")";
    }
}
