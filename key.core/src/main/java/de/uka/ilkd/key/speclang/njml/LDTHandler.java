package de.uka.ilkd.key.speclang.njml;

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

import javax.annotation.Nullable;
import java.util.Map;

public abstract class LDTHandler implements JMLOperatorHandler {

    protected final Services services;

    protected LDTHandler(Services services) {
        this.services = services;
    }

    @Nullable
    protected abstract Operator getOperator(Type promotedType, JMLOperator op);

    @Nullable
    protected static Operator getOperatorFromMap(@Nullable Map<JMLOperator, Operator> opMap,
            JMLOperator op) {
        if (opMap == null) {
            // we are not responsible for the type
            return null;
        }
        Operator jop = opMap.get(op);
        if (jop == null) {
            // TODO should that perhaps be an exception?
            return null;
        }
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
        Operator op = getOperator(promotedType.getJavaType(), jop);
        if (op == null) {
            return null;
        }

        Term a = promote(left.getTerm(), promotedType);
        Term b = promote(right.getTerm(), promotedType);
        Term resultTerm = services.getTermFactory().createTerm(op, a, b);
        if (OverloadedOperatorHandler.PREDICATES.contains(jop)) {
            // should be "formula", but apparently there is no KJT for that.
            return new SLExpression(resultTerm);
        } else {
            return new SLExpression(resultTerm, promotedType);
        }
    }

    private SLExpression buildUnary(JMLOperator jop, SLExpression left) {
        KeYJavaType type = left.getType();
        Operator op = getOperator(type.getJavaType(), jop);
        if (op == null) {
            return null;
        }
        Term resultTerm = services.getTermFactory().createTerm(op, left.getTerm());
        return new SLExpression(resultTerm, type);
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
