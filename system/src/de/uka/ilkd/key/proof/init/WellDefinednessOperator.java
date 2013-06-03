package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

public class WellDefinednessOperator {

    public static final TermBuilder TB = TermBuilder.DF;

    private final Services services;
    private final IntegerLDT intLDT;

    public WellDefinednessOperator(final Services services) {
        assert services != null;
        this.services = services;
        this.intLDT = services.getTypeConverter().getIntegerLDT();
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
            if (isDivision(t) || isModulo(t)) {
                return TB.and(TB.not(TB.equals(t.sub(1), TB.zero(services))),
                              wd(t.sub(0), t.sub(1)));
            } else {
                return wd(t.sub(0), t.sub(1));
            }
        }
        // TODO: Floating point types, \bigint and \real

        // TODO: Conditional Expression, Type Expression, Type Cast

        // TODO: Reference Expressions ...

        else if (isInv(t)) {
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
        assert op instanceof Function;
        Function f = (Function)op;

        if (op.toString().equalsIgnoreCase("Z")
                || intLDT.hasLiteralFunction(f)) {
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
        Term guard = TB.and(wd(a), TB.equals(a, TB.ff()));
        Term wd = TB.and(wd(a), wd(b));
        return TB.or(guard, wd);
    }

    private Term inv(Term a) {
        // FIXME: What shall we do with <inv>?
        return TB.tt();
    }

    private boolean isInv(Term t) {
        Operator op = t.op();
        return op.name().toString().endsWith("<inv>");
    }

    private boolean isEqualityPredicateOp(Term t) {
        Operator op = t.op();
        if (op.equals(op.equals(Equality.EQUALS))) {
            return true;
        } else if (!(op instanceof Function)) {
            return false;
        } else if (op.equals(intLDT.getLessThan())) {
            return true;
        } else if (op.equals(intLDT.getLessOrEquals())) {
            return true;
        } else if (op.equals(intLDT.getGreaterThan())) {
            return true;
        } else if (op.equals(intLDT.getGreaterOrEquals())) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isUnaryNumericalOp(Term t) {
        Operator op = t.op();

        if (op.equals(intLDT.getJavaUnaryMinusInt())
                || op.equals(intLDT.getJavaUnaryMinusLong())) {
            return true;
        } else if (op.equals(intLDT.getJavaBitwiseNegation())) {
            return true;
        } else if(op.toString().equalsIgnoreCase("Z")) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isNumericalOp(Term t) {
        if (isAddition(t) || isSubtraction(t)
                || isMultiplication(t) || isDivision(t) || isModulo(t)
                || isShiftOp(t) || isBitwiseAnd(t) || isBitwiseOr(t) || isBitwiseXOr(t)) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isAddition(Term t) {
        Operator op = t.op();
        if (op.equals(intLDT.getAdd())
                || op.equals(intLDT.getJavaAddInt())
                || op.equals(intLDT.getJavaAddLong())) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isSubtraction(Term t) {
        Operator op = t.op();
        if (op.equals(intLDT.getSub())
                || op.equals(intLDT.getJavaSubInt())
                || op.equals(intLDT.getJavaSubLong())) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isMultiplication(Term t) {
        Operator op = t.op();
        if (op.equals(intLDT.getMul())
                || op.equals(intLDT.getJavaMulInt())
                || op.equals(intLDT.getJavaMulLong())) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isDivision(Term t) {
        Operator op = t.op();
        if (op.equals(intLDT.getDiv())
                || op.equals(intLDT.getJavaDivInt())
                || op.equals(intLDT.getJavaDivLong())) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isModulo(Term t) {
        Operator op = t.op();
        if (op.equals(intLDT.getMod())
                || op.equals(intLDT.getJavaMod())) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isShiftOp(Term t) {
        Operator op = t.op();

        if (op.equals(intLDT.getJavaShiftLeftInt())
                || op.equals(intLDT.getJavaShiftLeftLong())
                || op.equals(intLDT.getJavaShiftRightInt())
                || op.equals(intLDT.getJavaShiftRightLong())
                || op.equals(intLDT.getJavaUnsignedShiftRightInt())
                || op.equals(intLDT.getJavaUnsignedShiftRightLong())) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isBitwiseAnd(Term t) {
        Operator op = t.op();
        if (op.equals(intLDT.getJavaBitwiseAndInt())
                || op.equals(intLDT.getJavaBitwiseAndLong())) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isBitwiseOr(Term t) {
        Operator op = t.op();
        if (op.equals(intLDT.getJavaBitwiseOrInt())
                || op.equals(intLDT.getJavaBitwiseOrLong())) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isBitwiseXOr(Term t) {
        Operator op = t.op();
        if (op.equals(intLDT.getJavaBitwiseXOrInt())
                || op.equals(intLDT.getJavaBitwiseXOrLong())) {
            return true;
        } else {
            return false;
        }
    }
}