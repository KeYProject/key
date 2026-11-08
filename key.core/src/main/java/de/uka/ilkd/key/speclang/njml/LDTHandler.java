/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.njml;

import java.util.Map;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperatorHandler;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
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

    public @Nullable SLExpression build(JMLOperator jop, SLExpression left,
            @Nullable SLExpression right)
            throws SLTranslationException {
        if (OverloadedOperatorHandler.UNARY_OPERATORS.contains(jop)) {
            return buildUnary(jop, left);
        }

        SLExpression rhs = Objects.requireNonNull(right,
            "binary operator called without right operand");
        KeYJavaType promotedType = services.getTypeConverter().getPromotedType(
            Objects.requireNonNull(left.getType(), "left operand carries no type"),
            Objects.requireNonNull(rhs.getType(), "right operand carries no type"));
        TypedOperator top = getOperator(
            Objects.requireNonNull(promotedType.getJavaType(), "no promoted type found"), jop);
        if (top == null) {
            return null;
        }

        JTerm a = promote(Objects.requireNonNull(left.getTerm(), "left operand is no term"),
            promotedType);
        JTerm b = promote(Objects.requireNonNull(rhs.getTerm(), "right operand is no term"),
            promotedType);
        JTerm resultTerm = services.getTermFactory().createTerm(top.operator, a, b);
        if (OverloadedOperatorHandler.PREDICATES.contains(jop)) {
            // should be "formula", but apparently there is no KJT for that.
            return new SLExpression(resultTerm);
        } else {
            return new SLExpression(resultTerm, top.type);
        }
    }

    private @Nullable SLExpression buildUnary(JMLOperator jop, SLExpression left) {
        KeYJavaType type = Objects.requireNonNull(left.getType(), "no operand type available");
        TypedOperator top = getOperator(
            Objects.requireNonNull(type.getJavaType(), "no operand Java type available"), jop);
        if (top == null) {
            return null;
        }
        JTerm resultTerm = services.getTermFactory().createTerm(top.operator,
            Objects.requireNonNull(left.getTerm(), "operand is no term"));
        return new SLExpression(resultTerm, top.type);
    }

    private JTerm promote(JTerm term, KeYJavaType resultType) {
        Sort targetSort = Objects.requireNonNull(resultType.getSort(), "no result sort available");
        if (term.sort() != targetSort) {
            return services.getTermBuilder().cast(targetSort, term);
        } else {
            return term;
        }
    }
}
