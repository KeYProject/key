/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.JAbstractSortedOperator;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;

/**
 * This variable condition checks if an instantiation is a constant formula or term, i.e. its arity
 * is equal to zero.
 *
 * @author Michael Kirsten
 */
public class ConstantCondition extends VariableConditionAdapter {

    private final JAbstractSortedOperator t;
    private final boolean negated;

    public ConstantCondition(JAbstractSortedOperator t, boolean negated) {
        this.t = t;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SyntaxElement instCandidate, SVInstantiations instMap,
            Services services) {
        if ((!(var instanceof TermSV) || var != this.t)
                && (!(var instanceof FormulaSV) || var != this.t)) {
            return true;
        }
        if (var instanceof TermSV) {
            JTerm tInst = instMap.getInstantiation((TermSV) t);
            boolean atomic = (tInst.arity() == 0);
            return negated != atomic;
        }
        if (var instanceof FormulaSV) {
            JTerm tInst = instMap.getInstantiation((FormulaSV) t);
            boolean atomic = (tInst.arity() == 0);
            return negated != atomic;
        }
        return false;
    }

    @Override
    public String toString() {
        return (negated ? "\\not" : "") + "\\isConstant (" + t + ")";
    }
}
