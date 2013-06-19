package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfExThenElse;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;

public class WellDefinednessOperator {

    public static final TermBuilder TB = TermBuilder.DF;

    private final Services services;
    private final IntegerLDT intLDT;
    private final HeapLDT heapLDT;
    private final LocSetLDT locSetLDT;

    public WellDefinednessOperator(final Services services) {
        assert services != null;
        this.services = services;
        this.intLDT = services.getTypeConverter().getIntegerLDT();
        this.heapLDT = services.getTypeConverter().getHeapLDT();
        this.locSetLDT = services.getTypeConverter().getLocSetLDT();
    }

    // TODO: What about change of system state after valuation?
    // TODO: select-terms? variables?
    public Term wd(Term t) {
        Operator op = t.op();
        int subs = t.arity(); // number of sub terms
        // Primary expressions
        if (subs == 0) {
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
            // Reverse implication is parsed to an equivalent disjunction and thus
            // does not have to be considered separately
            assert subs == 2;
            return imp(t.sub(0), t.sub(1));
        } else if (op.equals(Equality.EQV)
                || op.equals(Equality.EQUALS)) {
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
            return num(t);
        } else if (isNumericalOp(t)) {
            assert subs == 2;
            if ((isDivision(t) || isModulo(t)) && !isFloatOrDouble(t)) {
                return TB.and(TB.not(TB.equals(t.sub(1), TB.zero(services))),
                              wd(t.sub(0), t.sub(1)));
            } else {
                return wd(t.sub(0), t.sub(1));
            }
        }
        // Conditional expression
        else if (op.equals(IfThenElse.IF_THEN_ELSE)
                || op.equals(IfExThenElse.IF_EX_THEN_ELSE)) {
            assert subs == 3;
            return cond(t.sub(0), t.sub(1), t.sub(2));
        }
        // Type Expressions:
        // \type - not necessary (only supported by KeY for a special case)
        // \typeof - done by parser
        // \elemtype - not supported by KeY

        // TODO: Reference Expressions ...
        else if (op.equals(locSetLDT.getSingleton())) {
            assert subs == 2;
            return wd(t.sub(0));
        } else if (op.equals(heapLDT.getSelect(t.sort(), services))) {
            assert subs == 3;
            return TB.and(TB.and(heap(t.sub(0)), wd(t.sub(1))), wd(t.sub(2)));
        }

        // Logical Quantifiers
        else if (op.equals(Quantifier.ALL)) {
            assert subs == 3;
            return all(t);
        } else if (op.equals(Quantifier.EX)) {
            assert subs == 3;
            return ex(t);
        }

        // Generalized Quantifiers
        else if (op.equals(intLDT.getBsum())) {
            assert subs == 3;
            return bSum(t);
        } else if (op.equals(intLDT.getBprod())) {
            assert subs == 3;
            return bProd(t);
        }
        // max, min and num_of already done in IF_EX_THEN_ELSE and bsum

        else if (isInv(t)) {
            return inv(t);
        }
        // TODO: How to test if t is a fresh variable?
        else {
            throw new TermCreationException("Unknown term!" + '\n' +
                    "Operator: " + op.toString() + '\n' +
                    "With " + subs + " subterms" + '\n' +
                    "Term: " + t.toString());
        }
    }

    private Term wd(Term a, Term b) {
        assert a.sort().equals(b.sort())
            || a.sort().extendsTrans(b.sort())
            || b.sort().extendsTrans(a.sort());
        return TB.and(wd(a), wd(b));
    }

    // true, false
    private Term primaryExpr(Term e) {
        int subs = e.arity();
        Operator op = e.op();
        assert subs == 0;

        if (op.equals(Junctor.TRUE) || op.equals(Junctor.FALSE)) {
            return TB.tt();
        } else if (op.equals(heapLDT.getNull())) {
            return TB.tt();
        } else if (op instanceof ParsableVariable) {
            return TB.tt();
        } else if (op instanceof Function) {
            return TB.tt();
        }
        return TB.ff();
    }

    // a || b
    private Term or(Term a, Term b) {
        Term guard = TB.and(wd(a), a);
        Term wd = TB.and(wd(a), wd(b));
        return TB.or(guard, wd);
    }

    // a && b
    private Term and(Term a, Term b) {
        Term guard = TB.and(wd(a), TB.not(a));
        Term wd = TB.and(wd(a), wd(b));
        return TB.or(guard, wd);
    }

    // a ==> b
    private Term imp(Term a, Term b) {
        Term guard = TB.and(wd(a), TB.not(a));
        Term wd = TB.and(wd(a), wd(b));
        return TB.or(guard, wd);
    }

    private Term cond(Term a, Term b, Term c) {
        return TB.or(wd(a, wd(a, b)),
                     wd(TB.not(a), wd(a, c)));
    }

    private Term inv(Term t) {
        int subs = t.arity();
        assert isInv(t);
        assert subs == 2;
        return TB.and(wd(t.sub(0)),heap(t.sub(1)));
    }

    private boolean isInv(Term t) {
        Operator op = t.op();
        return op.toString().endsWith("<inv>");
    }

    private Term num(Term t) {
        int subs = t.arity();
        Operator op = t.op();

        assert subs <= 1;
        assert op instanceof Function;
        Function f = (Function)op;

        if (isUnaryNumericalOp(t)
                && !f.equals(intLDT.getNumberTerminator())) {
            assert subs == 1;
            // Type cast (only numerical type casts supported,
            //            since domains for other casts unclear)
            if (isCastOp(t)) {
                final String min;
                final String max;
                if (f.equals(intLDT.getJavaCastByte())) {
                    min = (new Byte(Byte.MIN_VALUE)).toString();
                    max = (new Byte(Byte.MAX_VALUE)).toString();
                } else if (f.equals(intLDT.getJavaCastChar())) {
                    min = (new Character(Character.MIN_VALUE)).toString();
                    max = (new Character(Character.MAX_VALUE)).toString();
                } else if (f.equals(intLDT.getJavaCastInt())) {
                    min = (new Integer(Integer.MIN_VALUE)).toString();
                    max = (new Integer(Integer.MAX_VALUE)).toString();
                } else if (f.equals(intLDT.getJavaCastLong())) {
                    min = (new Long(Long.MIN_VALUE)).toString();
                    max = (new Long(Long.MAX_VALUE)).toString();
                } else if (f.equals(intLDT.getJavaCastShort())) {
                    min = (new Short(Short.MIN_VALUE)).toString();
                    max = (new Short(Short.MAX_VALUE)).toString();
                } else {
                    assert false; // Unknown cast
                    min = "";
                    max = "";
                }
                return TB.and(num(t.sub(0)),
                              TB.and(TB.lt(TB.zTerm(services, min), t, services),
                                     TB.gt(TB.zTerm(services, max), t, services)));
            } else {
                return num(t.sub(0));
            }
        } else {
            assert f.equals(intLDT.getNumberTerminator());
            assert subs == 0;
            return TB.tt();
        }
    }

    private Term all(Term t) {
        // FIXME
        return null;
    }

    private Term ex(Term t) {
        // FIXME
        return null;
    }

    private Term bSum(Term t) {
        // FIXME
        return null;
    }

    private Term bProd(Term t) {
        // FIXME
        return null;
    }

    private Term heap(Term t) {
        int subs = t.arity();
        Operator op = t.op();
        assert subs == 0;

        if (op.equals(heapLDT.getHeap())) {
            return TB.tt();
        } else {
            return TB.ff();
        }
    }

    private boolean isCastOp(Term t) {
        int subs = t.arity();
        Operator op = t.op();

        if (subs > 1 || !(op instanceof Function)) {
            return false;
        }
        Function f = (Function)op;

        if (f.equals(intLDT.getJavaCastByte()) || f.equals(intLDT.getJavaCastChar())
                || f.equals(intLDT.getJavaCastInt()) || f.equals(intLDT.getJavaCastLong())
                || f.equals(intLDT.getJavaCastShort())) {
            return true;
        } else {
            return false;
        }
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
        // Floating point operations not supported
        if (op.equals(intLDT.getJavaUnaryMinusInt())
                || op.equals(intLDT.getJavaUnaryMinusLong())
                || op.equals(intLDT.getNegativeNumberSign())) {
            assert isIntegerOrChar(t) || isBigIntOrReal(t);
            return true;
        } else if (op.equals(intLDT.getJavaBitwiseNegation())) {
            assert isIntegerOrChar(t);
            return true;
        } else if (op.equals(intLDT.getJavaCastByte())) {
            assert intLDT.getType(t).equals(PrimitiveType.JAVA_BYTE);
            return true;
        } else if (op.equals(intLDT.getJavaCastChar())) {
            assert intLDT.getType(t).equals(PrimitiveType.JAVA_CHAR);
            return true;
        } else if (op.equals(intLDT.getJavaCastInt())) {
            assert intLDT.getType(t).equals(PrimitiveType.JAVA_INT);
            return true;
        } else if (op.equals(intLDT.getJavaCastLong())) {
            assert intLDT.getType(t).equals(PrimitiveType.JAVA_LONG);
            return true;
        } else if (op.equals(intLDT.getJavaCastShort())) {
            assert intLDT.getType(t).equals(PrimitiveType.JAVA_SHORT);
            return true;
        } else if (op.equals(intLDT.getNumberSymbol())) {
            return true;
        } else if (op instanceof Function
                && intLDT.hasLiteralFunction((Function)op)) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isIntegerOrChar(Term a) {
        Type t = intLDT.getType(a);
        if (t.equals(PrimitiveType.JAVA_INT) || t.equals(PrimitiveType.JAVA_LONG)
                || t.equals(PrimitiveType.JAVA_BYTE) || t.equals(PrimitiveType.JAVA_SHORT)
                || t.equals(PrimitiveType.JAVA_CHAR)) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isFloatOrDouble(Term a) {
        Type t = services.getTypeConverter().getModelFor(a.sort()).getType(a);
        if (t.equals(PrimitiveType.JAVA_FLOAT) || t.equals(PrimitiveType.JAVA_DOUBLE)) {
            return true;
        } else {
            return false;
        }
    }

    private boolean isBigIntOrReal(Term a) {
        // \real is not supported
        Type t = intLDT.getType(a);
        return t.equals(PrimitiveType.JAVA_BIGINT);
    }

    private boolean isNumericalOp(Term t) {
        // Floating point operations not supported
        if (isAddition(t) || isSubtraction(t)
                || isMultiplication(t) || isDivision(t) || isModulo(t)) {
            assert isIntegerOrChar(t) || isBigIntOrReal(t);
            return true;
        } else if (isShiftOp(t) || isBitwiseAnd(t)
                || isBitwiseOr(t) || isBitwiseXOr(t)) {
            assert isIntegerOrChar(t);
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