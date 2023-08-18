/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.*;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * This class is used to resolve arithmetic operations to {@link SLExpression}s. These are overladed
 * for different primitive types.
 *
 * It delegates to the {@link JMLOperatorHandler}s registered in the class.
 *
 * Numeric promotion plays into it, too.
 *
 * @author Alexander Weigl
 * @version 1 (1/9/22)
 */
public class OverloadedOperatorHandler {

    /**
     * Enumeration of all arithmetic operators which can be overloaded.
     */
    public enum JMLOperator {
        /* binaries */
        ADD("+"), SUBTRACT("-"), MULT("*"), DIVISION("/"), MODULO("%"), BITWISE_AND("&"),
        BITWISE_OR("|"), BITWISE_XOR("^"), SHIFT_RIGHT(">>"), SHIFT_LEFT("<<"),
        UNSIGNED_SHIFT_RIGHT(">>>"),
        /* unaries */
        BITWISE_NEGATE("???"), UNARY_MINUS("-"),
        /* predicates */
        LT("<"), GT(">"), GTE(">="), LTE("<=");

        private final String image;

        JMLOperator(String image) {
            this.image = image;
        }

        public static JMLOperator get(String image) {
            for (JMLOperator value : JMLOperator.values()) {
                if (value.image.equals(image)) {
                    return value;
                }
            }
            throw new NoSuchElementException("There is no JML operator for " + image);
        }

        public String getImage() {
            return image;
        }
    }

    /**
     * The collection of those operators which take one (not two) arguments.
     */
    public static final Set<JMLOperator> UNARY_OPERATORS =
        EnumSet.of(JMLOperator.BITWISE_NEGATE, JMLOperator.UNARY_MINUS);

    /**
     * The collection of those operators whose result is expected to be boolean.
     */
    public static final Set<JMLOperator> PREDICATES =
        EnumSet.of(JMLOperator.LT, JMLOperator.LTE, JMLOperator.GT, JMLOperator.GTE);

    /**
     * Functional interface that defines how JML arithmetic operators are overloaded for particular
     * arguments.
     */
    public interface JMLOperatorHandler {
        /**
         * Apply the provided arguments to the operator which corresponds to the given JML operator.
         *
         * @param op the JML operator
         * @param left left side of the binary expression
         * @param right right side of the binary expression, null if op is unary.
         * @return null if this handler is not able to do the translation.
         * @throws SLTranslationException if translation fails (incompatible types e.g.)
         */
        @Nullable
        SLExpression build(JMLOperator op, SLExpression left, SLExpression right)
                throws SLTranslationException;
    }

    private final List<JMLOperatorHandler> handlers = new ArrayList<>();
    private final IntegerHandler integerHandler;

    public OverloadedOperatorHandler(Services services, SpecMathMode specMathMode) {
        this.integerHandler = new IntegerHandler(services, specMathMode);

        handlers.add(new BinaryBooleanHandler(services));
        // handlers.add(new SequenceHandler(services));
        // handlers.add(new LocSetHandler(services));
        handlers.add(this.integerHandler);
        handlers.add(new FloatHandler(services));
        handlers.add(new DoubleHandler(services));
        // handlers.add(new RealHandler(services));
    }

    /**
     * Sets the spec math mode and returns the previous mode
     *
     * @param specMathMode new spec math mode
     * @return old spec math mode
     */
    public SpecMathMode replaceSpecMathMode(SpecMathMode specMathMode) {
        return integerHandler.replaceSpecMathMode(specMathMode);
    }

    /**
     * @return the spec math mode
     */
    public SpecMathMode getSpecMathMode() {
        return integerHandler.getSpecMathMode();
    }

    @Nullable
    public SLExpression build(JMLOperator op, SLExpression left, SLExpression right)
            throws SLTranslationException {
        for (JMLOperatorHandler handler : handlers) {
            var term = handler.build(op, left, right);
            if (term != null) {
                return term;
            }
        }
        return null;
    }


    public static class SequenceHandler implements JMLOperatorHandler {
        private final SeqLDT ldtSequence;
        private final TermBuilder tb;

        public SequenceHandler(Services services) {
            ldtSequence = services.getTypeConverter().getSeqLDT();
            tb = services.getTermBuilder();
        }

        @Nullable
        @Override
        public SLExpression build(JMLOperator op, SLExpression left, SLExpression right)
                throws SLTranslationException {
            if (left.getTerm().sort() == ldtSequence.targetSort()
                    && right.getTerm().sort() == ldtSequence.targetSort()) {
                if (op == JMLOperator.ADD) {
                    return new SLExpression(tb.seqConcat(left.getTerm(), right.getTerm()));
                }
            }
            return null;
        }
    }

    public static class LocSetHandler implements JMLOperatorHandler {
        private final LocSetLDT ldt;
        private final TermBuilder tb;

        public LocSetHandler(Services services) {
            ldt = services.getTypeConverter().getLocSetLDT();
            tb = services.getTermBuilder();
        }

        @Nullable
        @Override
        public SLExpression build(JMLOperator op, SLExpression left, SLExpression right)
                throws SLTranslationException {
            final var l = left.getTerm();
            final var r = right.getTerm();
            if (l.sort() == ldt.targetSort() && r.sort() == ldt.targetSort()) {
                switch (op) {
                case ADD:
                case BITWISE_OR:
                    return new SLExpression(tb.union(l, r));
                case SUBTRACT:
                    return new SLExpression(tb.setMinus(l, r));
                case BITWISE_AND:
                    return new SLExpression(tb.intersect(l, r));
                case LT:
                    return new SLExpression(tb.subset(l, r));
                case LTE:
                    return new SLExpression(tb.and(tb.subset(l, r), tb.equals(l, r)));
                case GT:
                    return new SLExpression(tb.subset(r, l));
                case GTE:
                    return new SLExpression(tb.and(tb.subset(r, l), tb.equals(l, r)));
                }
            }
            return null;
        }
    }

    private static class BinaryBooleanHandler implements JMLOperatorHandler {
        private final Sort sortBoolean;
        private final TermBuilder tb;

        public BinaryBooleanHandler(Services services) {
            sortBoolean = services.getTypeConverter().getBooleanLDT().targetSort();
            tb = services.getTermBuilder();
        }

        @Nullable
        @Override
        public SLExpression build(JMLOperator op, SLExpression left, SLExpression right)
                throws SLTranslationException {
            if ((left.getTerm().sort() == sortBoolean || left.getTerm().sort() == Sort.FORMULA)
                    && (right.getTerm().sort() == sortBoolean
                            || right.getTerm().sort() == Sort.FORMULA)) {
                final var t1 = tb.convertToFormula(left.getTerm());
                final var t2 = tb.convertToFormula(right.getTerm());
                switch (op) {
                case BITWISE_AND:
                    return new SLExpression(tb.and(t1, t2));
                case BITWISE_OR:
                    return new SLExpression(tb.or(t1, t2));
                case BITWISE_XOR:
                    return new SLExpression(tb.or(tb.and(t1, tb.not(t2)), tb.and(tb.not(t1), t2)));
                }
            }
            return null;
        }
    }
}
