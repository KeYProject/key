/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This variable condition checks if an instantiation for a formula has sub formulas which are
 * formulas. It returns false for an arity equal to zero or no sub formulas. This is needed to
 * simplify distinguishing between different well-definedness operators in taclets, since the
 * difference exists only for formulas.
 *
 * @author Michael Kirsten
 *
 */
public class SubFormulaCondition extends VariableConditionAdapter {

    private final FormulaSV a;
    private final boolean negated;

    public SubFormulaCondition(FormulaSV a, boolean negated) {
        this.a = a;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate, SVInstantiations instMap,
            Services services) {
        if (!(var instanceof FormulaSV) || var != this.a) {
            return false;
        }
        Term tInst = (Term) instMap.getInstantiation(a);
        if (tInst.arity() == 0) {
            return negated;
        } else {
            for (Term sub : tInst.subs()) {
                if (sub.sort() == Sort.FORMULA) {
                    return !negated;
                }
            }
            return negated;
        }
    }

    @Override
    public String toString() {
        return (negated ? "\\not" : "") + "\\hasSubFormulas (" + a + ")";
    }
}
