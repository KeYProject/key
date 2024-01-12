/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * ensures that the given instantiation for the schema variable denotes a final field
 */
public final class FinalReferenceCondition extends VariableConditionAdapter {

    private final SchemaVariable reference;
    private final boolean negation;

    /**
     * the static reference condition checks if a suggested instantiation for a schema variable
     * denotes a static reference. The flag negation allows to reuse this condition for ensuring non
     * static references.
     */
    public FinalReferenceCondition(SchemaVariable reference, boolean negation) {
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
            } else if (subst instanceof ProgramVariable) {
                attribute = (ProgramVariable) subst;
            } else {
                return !negation;
            }
            return (negation ^ attribute.isFinal()) && !(attribute instanceof ProgramConstant);
        }
        return true;
    }


    @Override
    public String toString() {
        return (negation ? " \\not " : "") + "\\final(" + reference + ")";
    }
}
