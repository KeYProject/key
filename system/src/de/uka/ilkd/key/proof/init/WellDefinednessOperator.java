package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

public class WellDefinednessOperator {

    public static final WellDefinednessOperator WD = new WellDefinednessOperator();

    public static final TermBuilder TB = TermBuilder.DF;
    
    public WellDefinednessOperator() {
    }

    // TODO: What about change of system state after valuation?
    public Term wd(Term t) {
        Operator op = t.op();
        int subs = t.arity();
        // Primary expressions
        if (op.equals(Junctor.TRUE) || op.equals(Junctor.FALSE)) {
            assert subs == 0;
            return primaryExpr(t);
        }
        // Logical operators
        else if (op.equals(Junctor.NOT)) {
            assert subs == 1;
            return wd(t.sub(0));
        } else if (op.equals(Junctor.OR)) {
            assert subs == 2;
            return or(t.sub(0), t.sub(1));
        } else if (op.equals(Junctor.AND)) {
            assert subs == 2;
            return and(t.sub(0), t.sub(1));
        } else if (op.equals(Junctor.IMP)) {
            assert subs == 2;
            return imp(t.sub(0), t.sub(1));
        } else if (op.equals(AbstractTermTransformer.META_INT_XOR)
                || op.equals(AbstractTermTransformer.META_LONG_XOR)) {
        assert subs == 2;
        return wd(t.sub(0), t.sub(1));
        } else if (op.equals(Equality.EQV)) {
            assert subs == 2;
            return wd(t.sub(0), t.sub(1));
        }
        // Equality predicate operators
        else if (isEqualityPredicateOp(t)) {
            assert subs == 2;
            return wd(t.sub(0), t.sub(1));
        }
        // Numerical operators
        else if (isUnaryNumericalOp(t)) {
            assert subs == 1;
            return num(t.sub(0));
        } else if (isNumericalOp(t)) {
            assert subs == 2;
            if (notDivOrModOp(t) || valueNotZero(t.sub(1))) {
                return wd(t.sub(0), t.sub(1));
            } else {
                return TB.ff();
            }
        }
        // TODO: Floating point types, \bigint and \real

        // TODO: Conditional Expression, Type Expression, Type Cast

        // TODO: Reference Expressions ...

        else if (op.name().toString().endsWith("<inv>")) {
            // FIXME: What shall we do with <inv>?
            return inv(t);
        } // TODO: How to test if t is a fresh variable?
        else {
            throw new TermCreationException("Unknown term!" + '\n' +
                                            "Operator: " + op.toString() + '\n' +
                                            "Term: " + t.toString());
        }
    }

    private Term wd(Term a, Term b) {
        return TB.and(wd(a), wd(b));
    }

    // true, false
    private Term primaryExpr(Term a) {
        int subs = a.arity();
        assert subs == 0;
        return TB.tt();
    }

    private Term num(Term t) {
        int subs = t.arity();
        Operator op = t.op();
        assert subs <= 1;

        if (op.toString().equalsIgnoreCase("Z")) {
            return TB.tt();
        } else {
            return wd(t);
        }
    }

    // a || b
    private Term or(Term a, Term b) {
        Term guard = TB.and(wd(a), TB.equals(a, TB.tt()));
        Term wd = TB.and(wd(a), wd(b));
        return TB.or(guard, wd);
    }

    // a && b
    private Term and(Term a, Term b) {
        Term guard = TB.and(wd(a), TB.equals(a, TB.ff()));
        Term wd = TB.and(wd(a), wd(b));
        return TB.or(guard, wd);
    }

    // a ==> b
    private Term imp(Term a, Term b) {
        // What about a <== b ?
        Term guard = TB.and(wd(a), TB.equals(a, TB.ff()));
        Term wd = TB.and(wd(a), wd(b));
        return TB.or(guard, wd);
    }

    private Term inv(Term a) {
        return TB.tt();
    }

    boolean isEqualityPredicateOp(Term t) {
        throw new UnsupportedOperationException("Equality predicate operators not supported." +
                                                '\n' + "The operator was " + t.op().toString() +
                                                ".");
    }

    boolean isUnaryNumericalOp(Term t) {
        throw new UnsupportedOperationException("Unary numerical operators not supported." +
                                                '\n' + "The operator was " + t.op().toString() +
                                                ".");
    }

    boolean isNumericalOp(Term t) {
        throw new UnsupportedOperationException("Numerical operators not supported." +
                                                '\n' + "The operator was " + t.op().toString() +
                                                ".");
    }

    boolean notDivOrModOp(Term t) {
        throw new UnsupportedOperationException("Numerical operators not supported." +
                                                '\n' + "The operator was " + t.op().toString() +
                                                ".");
    }

    boolean valueNotZero(Term t) {
        throw new UnsupportedOperationException("Numerical operators not supported." +
                                                '\n' + "The operator was " + t.op().toString() +
                                                ".");
    }

    public static class Serviced extends WellDefinednessOperator {
        protected final Services services;

        public Serviced(final Services services) {
            assert services != null;
            this.services = services;
        }

        @Override
        boolean isEqualityPredicateOp(Term t) {
            Operator op = t.op();
            if (op.equals(op.equals(Equality.EQUALS))) {
                return true;
            }
            assert op instanceof Function;
            IntegerLDT ldt = services.getTypeConverter().getIntegerLDT();

            if (op.equals(ldt.getLessThan())) {
                return true;
            } else if (op.equals(ldt.getLessOrEquals())) {
                return true;
            } else if (op.equals(ldt.getGreaterThan())) {
                return true;
            } else if (op.equals(ldt.getGreaterOrEquals())) {
                return true;
            } else {
                return false;
            }
        }

        @Override
        boolean isUnaryNumericalOp(Term t) {
            Operator op = t.op();
            IntegerLDT ldt = services.getTypeConverter().getIntegerLDT();

            if (op.equals(ldt.getJavaUnaryMinusInt())
                    || op.equals(ldt.getJavaUnaryMinusLong())) {
                return true;
            } else if (op.equals(ldt.getJavaBitwiseNegation())) {
                return true;
            } else if(op.toString().equalsIgnoreCase("Z")) {
                return true;
            } else {
                return false;
            }
        }

        @Override
        boolean isNumericalOp(Term t) {
            Operator op = t.op();
            IntegerLDT ldt = services.getTypeConverter().getIntegerLDT();

            if (op.equals(ldt.getAdd())
                    || op.equals(ldt.getJavaAddInt())
                    || op.equals(ldt.getJavaAddLong())) {
                return true;
            } else if (op.equals(ldt.getSub())
                    || op.equals(ldt.getJavaSubInt())
                    || op.equals(ldt.getJavaSubLong())) {
                return true;
            } else if (op.equals(ldt.getMul())
                    || op.equals(ldt.getJavaMulInt())
                    || op.equals(ldt.getJavaMulLong())) {
                return true;
            } else if (op.equals(ldt.getDiv())
                    || op.equals(ldt.getJavaDivInt())
                    || op.equals(ldt.getJavaDivLong())) {
                return true;
            } else if (op.equals(ldt.getMod())
                    || op.equals(ldt.getJavaMod())) {
                return true;
            } else if (op.equals(ldt.getJavaShiftLeftInt())
                    || op.equals(ldt.getJavaShiftLeftLong())) {
                return true;
            } else if (op.equals(ldt.getJavaShiftRightInt())
                    || op.equals(ldt.getJavaShiftRightLong())) {
                return true;
            } else if (op.equals(ldt.getJavaUnsignedShiftRightInt())
                    || op.equals(ldt.getJavaUnsignedShiftRightLong())) {
                return true;
            } else if (op.equals(ldt.getJavaBitwiseAndInt())
                    || op.equals(ldt.getJavaBitwiseAndLong())) {
                return true;
            } else if (op.equals(ldt.getJavaBitwiseOrInt())
                    || op.equals(ldt.getJavaBitwiseOrLong())) {
                return true;
            } else if (op.equals(ldt.getJavaBitwiseXOrInt())
                    || op.equals(ldt.getJavaBitwiseXOrLong())) {
                return true;
            } else {
                return false;
            }
        }

        @Override
        boolean notDivOrModOp(Term t) {
            Operator op = t.op();
            IntegerLDT ldt = services.getTypeConverter().getIntegerLDT();

            if (op.equals(ldt.getDiv())
                    || op.equals(ldt.getJavaDivInt())
                    || op.equals(ldt.getJavaDivLong())) {
                return false;
            } else if (op.equals(ldt.getMod())
                    || op.equals(ldt.getJavaMod())) {
                return false;
            } else {
                return true;
            }
        }

        @Override
        boolean valueNotZero(Term t) {
            int subs = t.arity();
            IntegerLDT ldt = services.getTypeConverter().getIntegerLDT();
            assert subs == 1;

            ldt.zero();
            if (t.equals(ldt.zero())) {
                return false;
            } else {
                return true;
            }
        }
    }
}