/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * This variable condition checks if a context is affected by the strictfp modifier
 */
public final class InStrictFp extends VariableConditionAdapter {

    private final boolean negated;

    public InStrictFp(boolean negation) {
        this.negated = negation;
    }

    public boolean isNegated() {
        return negated;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate, SVInstantiations instMap,
            Services services) {

        ExecutionContext ec = instMap.getExecutionContext();

        if (ec == null) {
            return negated;
        } else {
            IProgramMethod methodContext = ec.getMethodContext();
            boolean strictfpClass = true;

            try {
                Type t = ec.getTypeReference().getKeYJavaType().getJavaType();
                if (t instanceof ClassDeclaration) {
                    strictfpClass = ((ClassDeclaration) t).isStrictFp();
                } else {
                    strictfpClass = false;
                }
            } catch (NullPointerException e) {
                strictfpClass = false;
            }

            final boolean isInStrictFp = strictfpClass || methodContext.isStrictFp();
            return negated != isInStrictFp;
        }
    }


    @Override
    public String toString() {
        String prefix = negated ? "\\not" : "";
        return prefix + "\\isStrictFp";
    }
}
