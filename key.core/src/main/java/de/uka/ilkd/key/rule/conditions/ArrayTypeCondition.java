/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * This variable condition checks if an instantiation is an array.
 *
 * @author mulbrich
 * @since 2006-12-03
 */
public final class ArrayTypeCondition extends VariableConditionAdapter {

    private final SchemaVariable var;
    private final boolean negated;

    /**
     * creates an instance of this condition checking if an instantiation of a schema variable is an
     * array or not
     *
     * @param var the SchemaVariable to be checked
     * @param negated if the result is to be negated upon finding
     */
    public ArrayTypeCondition(SchemaVariable var, boolean negated) {
        this.var = var;
        this.negated = negated;
    }


    @Override
    public boolean check(SchemaVariable var, SVSubstitute candidate, SVInstantiations svInst,
            Services services) {
        if (var != this.var) {
            return true;
        }
        Sort s = null;
        if (candidate instanceof Term) {
            s = ((Term) candidate).sort();
        } else if (candidate instanceof Expression) {
            s = ((Expression) candidate).getKeYJavaType(services, svInst.getExecutionContext())
                    .getSort();
        } else if (candidate instanceof TypeReference) {
            s = ((TypeReference) candidate).getKeYJavaType().getSort();
        }

        if (s == null) {
            return false;
        }

        boolean isArray = s instanceof ArraySort;

        return negated != isArray;

    }


    @Override
    public String toString() {
        return (negated ? "" : " \\not ") + "\\isArray(" + var + ")";
    }
}
