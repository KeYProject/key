/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class ArrayLengthCondition extends VariableConditionAdapter {

    private final SchemaVariable reference;
    private final boolean negation;


    public ArrayLengthCondition(SchemaVariable reference, boolean negation) {
        this.reference = reference;
        this.negation = negation;
    }


    @Override
    public boolean check(SchemaVariable var, SVSubstitute subst, SVInstantiations svInst,
            Services services) {
        if (var == reference) {
            ProgramVariable attribute;
            if (subst instanceof FieldReference) {
                attribute = ((FieldReference) subst).getProgramVariable();
            } else {
                attribute = (ProgramVariable) subst;
            }
            return negation ^ attribute == services.getJavaInfo().getArrayLength();
        }
        return true;
    }


    @Override
    public String toString() {
        return (negation ? " \\not " : "") + "\\isArrayLength(" + reference + ")";
    }
}
