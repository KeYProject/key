/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperatorHandler;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.Nullable;

public abstract class LDTHandler implements JMLOperatorHandler {
    /**
     * Pair (KJT, Operator)
     *
     * @param type type
     * @param operator operator
     */
    public record TypedOperator(KeYJavaType type, Operator operator) {
    }

    protected final Services services;

    protected LDTHandler(Services services) {
        this.services = services;
    }

    protected abstract @Nullable TypedOperator getOperator(Type promotedType, JMLOperator op);

    protected static @Nullable TypedOperator getOperatorFromMap(
            @Nullable Map<JMLOperator, TypedOperator> opMap,
            JMLOperator op) {
        if (opMap == null) {
            // we are not responsible for the type
            return null;
        }
        var jop = opMap.get(op);
        // TODO should that perhaps be an exception?
        return jop;
    }

    public @Nullable SLExpression build(JMLOperator jop, SLExpression left, SLExpression right)
            throws SLTranslationException {
        if (OverloadedOperatorHandler.UNARY_OPERATORS.contains(jop)) {
            return buildUnary(jop, left);
        }

        KeYJavaType promotedType =
            services.getTypeConverter().getPromotedType(left.getType(), right.getType());
        TypedOperator top = getOperator(promotedType.getJavaType(), jop);
        if (top == null) {
            return null;
        }

        Term a = promote(left.getTerm(), promotedType);
        Term b = promote(right.getTerm(), promotedType);
        Term resultTerm = services.getTermFactory().createTerm(top.operator, a, b);
        if (OverloadedOperatorHandler.PREDICATES.contains(jop)) {
            // should be "formula", but apparently there is no KJT for that.
            return new SLExpression(resultTerm);
        } else {
            return new SLExpression(resultTerm, top.type);
        }
    }

    private SLExpression buildUnary(JMLOperator jop, SLExpression left) {
        KeYJavaType type = left.getType();
        TypedOperator top = getOperator(type.getJavaType(), jop);
        if (top == null) {
            return null;
        }
        Term resultTerm = services.getTermFactory().createTerm(top.operator, left.getTerm());
        return new SLExpression(resultTerm, top.type);
    }

    private Term promote(Term term, KeYJavaType resultType) {
        Sort targetSort = resultType.getSort();
        if (term.sort() != targetSort) {
            return services.getTermBuilder().cast(targetSort, term);
        } else {
            return term;
        }
    }
}
