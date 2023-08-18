/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.Map;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperatorHandler;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

public abstract class LDTHandler implements JMLOperatorHandler {
    /**
     * Pair (KJT, Operator)
     */
    public static class TypedOperator {
        /** type */
        public final KeYJavaType type;
        /** operator */
        public final Operator operator;

        /** constructor */
        public TypedOperator(KeYJavaType type, Operator operator) {
            this.type = type;
            this.operator = operator;
        }
    }

    protected final Services services;

    protected LDTHandler(Services services) {
        this.services = services;
    }

    @Nullable
    protected abstract TypedOperator getOperator(Type promotedType, JMLOperator op);

    @Nullable
    protected static TypedOperator getOperatorFromMap(
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

    @Nullable
    public SLExpression build(JMLOperator jop, SLExpression left, SLExpression right)
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
