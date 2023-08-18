/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.FloatLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;

import org.key_project.util.ExtList;

public final class FloatLDT extends LDT implements FloatingPointLDT {

    public static final Name NAME = new Name("float");
    public static final Name FLOATLIT_NAME = new Name("FP");
    public static final Name NEGATIVE_LITERAL = new Name("javaUnaryMinusFloat");

    private final Function floatLit;
    private final Function lessThan;
    private final Function greaterThan;
    private final Function greaterOrEquals;
    private final Function lessOrEquals;

    private final Function eqFloat;

    private final Function javaUnaryMinusFloat;
    private final Function javaAddFloat;
    private final Function javaSubFloat;
    private final Function javaMulFloat;
    private final Function javaDivFloat;
    private final Function javaModFloat;

    private final Function javaMinFloat;
    private final Function javaMaxFloat;

    private final Function addFloatIEEE;
    private final Function subFloatIEEE;
    private final Function mulFloatIEEE;
    private final Function divFloatIEEE;
    private final Function absFloat;
    private final Function negFloat;

    private final Function isNormal;
    private final Function isSubnormal;
    private final Function isNaN;
    private final Function isZero;
    private final Function isNice;
    private final Function isInfinite;
    private final Function isNegative;
    private final Function isPositive;

    public FloatLDT(TermServices services) {
        super(NAME, services);

        floatLit = addFunction(services, FLOATLIT_NAME.toString());
        javaUnaryMinusFloat = addFunction(services, NEGATIVE_LITERAL.toString());
        lessThan = addFunction(services, "ltFloat");
        greaterThan = addFunction(services, "gtFloat");
        lessOrEquals = addFunction(services, "leqFloat");
        greaterOrEquals = addFunction(services, "geqFloat");
        eqFloat = addFunction(services, "eqFloat");

        javaAddFloat = addFunction(services, "javaAddFloat");
        javaSubFloat = addFunction(services, "javaSubFloat");
        javaMulFloat = addFunction(services, "javaMulFloat");
        javaDivFloat = addFunction(services, "javaDivFloat");
        javaModFloat = addFunction(services, "javaModFloat");
        javaMaxFloat = addFunction(services, "javaMaxFloat");
        javaMinFloat = addFunction(services, "javaMinFloat");

        addFloatIEEE = addFunction(services, "addFloat");
        subFloatIEEE = addFunction(services, "subFloat");
        mulFloatIEEE = addFunction(services, "mulFloat");
        divFloatIEEE = addFunction(services, "divFloat");
        absFloat = addFunction(services, "absFloat");
        negFloat = addFunction(services, "negFloat");

        isNormal = addFunction(services, "floatIsNormal");
        isSubnormal = addFunction(services, "floatIsSubnormal");
        isNaN = addFunction(services, "floatIsNaN");
        isZero = addFunction(services, "floatIsZero");
        isNice = addFunction(services, "floatIsNice");
        isInfinite = addFunction(services, "floatIsInfinite");
        isPositive = addFunction(services, "floatIsPositive");
        isNegative = addFunction(services, "floatIsNegative");
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term[] subs,
            Services services, ExecutionContext ec) {
        if (subs.length == 1) {
            return isResponsible(op, subs[0], services, ec);
        } else if (subs.length == 2) {
            return isResponsible(op, subs[0], subs[1], services, ec);
        }
        return false;
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term left, Term right,
            Services services, ExecutionContext ec) {
        return left != null && left.sort().extendsTrans(targetSort()) && right != null
                && right.sort().extendsTrans(targetSort())
                && getFunctionFor(op, services, ec) != null;
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term sub,
            TermServices services, ExecutionContext ec) {
        return sub != null && sub.sort().extendsTrans(targetSort()) && op instanceof Negative;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert lit instanceof FloatLiteral : "Literal '" + lit + "' is not a float literal.";
        String s = ((FloatLiteral) lit).getValue();
        float flValue = Float.parseFloat(s);
        return services.getTermBuilder().fpTerm(flValue);
    }

    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, Services services,
            ExecutionContext ec) {
        if (op instanceof GreaterThan) {
            return getGreaterThan();
        } else if (op instanceof LessThan) {
            return getLessThan();
        } else if (op instanceof GreaterOrEquals) {
            return getGreaterOrEquals();
        } else if (op instanceof LessOrEquals) {
            return getLessOrEquals();
        } else if (op instanceof Negative) {
            return getJavaUnaryMinus();
        } else if (op instanceof Plus) {
            return getJavaAdd();
        } else if (op instanceof Minus) {
            return getJavaSub();
        } else if (op instanceof Times) {
            return getJavaMul();
        } else if (op instanceof Divide) {
            return getJavaDiv();
        } else if (op instanceof Modulo) {
            return getJavaMod();
        } else {
            return null;
        }
    }

    @Override
    public Function getFunctionFor(String op, Services services) {
        switch (op) {
        case "gt":
            return getGreaterThan();
        case "geq":
            return getGreaterOrEquals();
        case "lt":
            return getLessThan();
        case "leq":
            return getLessOrEquals();
        case "div":
            return getDiv();
        case "mul":
            return getMul();
        case "add":
            return getAdd();
        case "sub":
            return getSub();
        case "neg":
            return getNeg();
        // Floating point extensions with "\fp_"
        case "nan":
            return getIsNaN();
        case "zero":
            return getIsZero();
        case "infinite":
            return getIsInfinite();
        case "nice":
            return getIsNice();
        case "abs":
            return getAbs();
        case "negative":
            return getIsNegative();
        case "positive":
            return getIsPositive();
        case "subnormal":
            return getIsSubnormal();
        case "normal":
            return getIsNormal();
        }
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return containsFunction(f) && (f.arity() == 0);
    }


    @Override
    public FloatLiteral translateTerm(Term t, ExtList children, Services services) {
        if (!containsFunction((Function) t.op())) {
            return null;
        }

        Function f = (Function) t.op();
        IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();

        if (f == floatLit) {
            // Use IntegerLDT to translate to literals
            String digits = intLDT.toNumberString(t.sub(0));
            int bits = Integer.parseUnsignedInt(digits);
            float f1 = Float.intBitsToFloat(bits);
            return new FloatLiteral(Float.toString(f1));
        }
        throw new RuntimeException("FloatLDT: Cannot convert term to program: " + t);
    }


    @Override
    public Type getType(Term t) {
        if (t.sort() == targetSort()) {
            return PrimitiveType.JAVA_FLOAT;
        } else {
            return null;
        }
    }

    public Function getFloatSymbol() {
        return floatLit;
    }

    public Function getLessThan() {
        return lessThan;
    }

    public Function getGreaterThan() {
        return greaterThan;
    }

    public Function getLessOrEquals() {
        return lessOrEquals;
    }

    public Function getGreaterOrEquals() {
        return greaterOrEquals;
    }

    public Function getEquals() {
        return eqFloat;
    }

    public Function getJavaUnaryMinus() {
        return javaUnaryMinusFloat;
    }

    public Function getJavaAdd() {
        return javaAddFloat;
    }

    public Function getJavaSub() {
        return javaSubFloat;
    }

    public Function getJavaMul() {
        return javaMulFloat;
    }

    public Function getJavaDiv() {
        return javaDivFloat;
    }

    public Function getJavaMod() {
        return javaModFloat;
    }

    public Function getJavaMin() {
        return javaMinFloat;
    }

    public Function getJavaMax() {
        return javaMaxFloat;
    }

    public Function getIsNormal() {
        return isNormal;
    }

    public Function getIsSubnormal() {
        return isSubnormal;
    }

    public Function getIsNaN() {
        return isNaN;
    }

    public Function getIsZero() {
        return isZero;
    }

    @Override
    public Function getIsNice() {
        return isNice;
    }

    public Function getIsInfinite() {
        return isInfinite;
    }

    public Function getIsPositive() {
        return isPositive;
    }

    public Function getIsNegative() {
        return isNegative;
    }

    public Function getAdd() {
        return addFloatIEEE;
    }

    public Function getSub() {
        return subFloatIEEE;
    }

    public Function getMul() {
        return mulFloatIEEE;
    }

    public Function getDiv() {
        return divFloatIEEE;
    }

    public Function getAbs() {
        return absFloat;
    }

    public Function getNeg() {
        return negFloat;
    }

}
