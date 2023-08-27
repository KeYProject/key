/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * This variable condition checks if a given type denotes an abstract class or interface type.
 */
public final class IsThisReference extends VariableConditionAdapter {

    private final boolean negated;
    private final ParsableVariable var;

    public IsThisReference(ParsableVariable var, boolean negation) {
        this.negated = negation;
        this.var = var;
        assert var.sort() == ProgramSVSort.VARIABLE;
    }


    public boolean isNegated() {
        return negated;
    }


    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate, SVInstantiations instMap,
            Services services) {
        if (var != this.var) {
            return true;
        }
        // boolean isThisRef = instMap.getInstantiation(var) instanceof ThisReference;
        boolean isThisRef = instCandidate instanceof ThisReference;
        return negated != isThisRef;
    }


    @Override
    public String toString() {
        String prefix = negated ? "\\not" : "";
        return prefix + "\\isThisReference (" + var + ")";
    }
}
