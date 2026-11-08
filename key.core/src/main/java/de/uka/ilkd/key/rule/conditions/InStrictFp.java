/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * This variable condition checks if a context is affected by the strictfp modifier
 */
@NullMarked
public final class InStrictFp extends VariableConditionAdapter {

    private final boolean negated;

    public InStrictFp(boolean negation) {
        this.negated = negation;
    }

    public boolean isNegated() {
        return negated;
    }

    @Override
    public boolean check(@Nullable SchemaVariable var, @Nullable SyntaxElement instCandidate,
            SVInstantiations instMap,
            Services services) {

        ExecutionContext ec = instMap.getExecutionContext();

        if (ec == null) {
            return negated;
        } else {
            IProgramMethod methodContext = ec.getMethodContext();
            boolean strictfpClass = true;

            try {
                Type t = Objects.requireNonNull(ec.getTypeReference().getKeYJavaType(),
                    "no KeYJavaType in execution context").getJavaType();
                if (t instanceof ClassDeclaration) {
                    strictfpClass = ((ClassDeclaration) t).isStrictFp();
                } else {
                    strictfpClass = false;
                }
            } catch (NullPointerException e) {
                strictfpClass = false;
            }

            final boolean isInStrictFp = strictfpClass
                    || Objects.requireNonNull(methodContext, "no method context").isStrictFp();
            return negated != isInStrictFp;
        }
    }


    @Override
    public String toString() {
        String prefix = negated ? "\\not" : "";
        return prefix + "\\isStrictFp";
    }
}
