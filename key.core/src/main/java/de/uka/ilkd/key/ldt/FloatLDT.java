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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.ExtList;

public final class FloatLDT extends LDT implements FloatingPointLDT {

    public static final Name NAME = new Name("float");
    public static final Name FLOATLIT_NAME = new Name("FP");
    public static final Name NEGATIVE_LITERAL = new Name("javaUnaryMinusFloat");

    private final JFunction floatLit;
    private final JFunction lessThan;
    private final JFunction greaterThan;
    private final JFunction greaterOrEquals;
    private final JFunction lessOrEquals;

    private final JFunction eqFloat;

    private final JFunction javaUnaryMinusFloat;
    private final JFunction javaAddFloat;
    private final JFunction javaSubFloat;
    private final JFunction javaMulFloat;
    private final JFunction javaDivFloat;
    private final JFunction javaModFloat;

    private final JFunction javaMinFloat;
    private final JFunction javaMaxFloat;

    private final JFunction addFloatIEEE;
    private final JFunction subFloatIEEE;
    private final JFunction mulFloatIEEE;
    private final JFunction divFloatIEEE;
    private final JFunction absFloat;
    private final JFunction negFloat;

    private final JFunction isNormal;
    private final JFunction isSubnormal;
    private final JFunction isNaN;
    private final JFunction isZero;
    private final JFunction isNice;
    private final JFunction isInfinite;
    private final JFunction isNegative;
    private final JFunction isPositive;

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
    public JFunction getFunctionFor(de.uka.ilkd.key.java.expression.Operator op,
            Services services,
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
    public JFunction getFunctionFor(String op, Services services) {
        return switch (op) {
        case "gt" -> getGreaterThan();
        case "geq" -> getGreaterOrEquals();
        case "lt" -> getLessThan();
        case "leq" -> getLessOrEquals();
        case "div" -> getDiv();
        case "mul" -> getMul();
        case "add" -> getAdd();
        case "sub" -> getSub();
        case "neg" -> getNeg();
        // Floating point extensions with "\fp_"
        case "nan" -> getIsNaN();
        case "zero" -> getIsZero();
        case "infinite" -> getIsInfinite();
        case "nice" -> getIsNice();
        case "abs" -> getAbs();
        case "negative" -> getIsNegative();
        case "positive" -> getIsPositive();
        case "subnormal" -> getIsSubnormal();
        case "normal" -> getIsNormal();
        default -> null;
        };
    }

    @Override
    public boolean hasLiteralFunction(JFunction f) {
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

    public JFunction getFloatSymbol() {
        return floatLit;
    }

    public JFunction getLessThan() {
        return lessThan;
    }

    public JFunction getGreaterThan() {
        return greaterThan;
    }

    public JFunction getLessOrEquals() {
        return lessOrEquals;
    }

    public JFunction getGreaterOrEquals() {
        return greaterOrEquals;
    }

    public JFunction getEquals() {
        return eqFloat;
    }

    public JFunction getJavaUnaryMinus() {
        return javaUnaryMinusFloat;
    }

    public JFunction getJavaAdd() {
        return javaAddFloat;
    }

    public JFunction getJavaSub() {
        return javaSubFloat;
    }

    public JFunction getJavaMul() {
        return javaMulFloat;
    }

    public JFunction getJavaDiv() {
        return javaDivFloat;
    }

    public JFunction getJavaMod() {
        return javaModFloat;
    }

    public JFunction getJavaMin() {
        return javaMinFloat;
    }

    public JFunction getJavaMax() {
        return javaMaxFloat;
    }

    public JFunction getIsNormal() {
        return isNormal;
    }

    public JFunction getIsSubnormal() {
        return isSubnormal;
    }

    public JFunction getIsNaN() {
        return isNaN;
    }

    public JFunction getIsZero() {
        return isZero;
    }

    @Override
    public JFunction getIsNice() {
        return isNice;
    }

    public JFunction getIsInfinite() {
        return isInfinite;
    }

    public JFunction getIsPositive() {
        return isPositive;
    }

    public JFunction getIsNegative() {
        return isNegative;
    }

    public JFunction getAdd() {
        return addFloatIEEE;
    }

    public JFunction getSub() {
        return subFloatIEEE;
    }

    public JFunction getMul() {
        return mulFloatIEEE;
    }

    public JFunction getDiv() {
        return divFloatIEEE;
    }

    public JFunction getAbs() {
        return absFloat;
    }

    public JFunction getNeg() {
        return negFloat;
    }

}
