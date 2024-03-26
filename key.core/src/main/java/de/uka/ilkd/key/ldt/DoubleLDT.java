/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.DoubleLiteral;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;

import org.key_project.logic.Name;
import org.key_project.util.ExtList;

public final class DoubleLDT extends LDT implements FloatingPointLDT {

    public static final Name NAME = new Name("double");
    public static final Name DOUBLELIT_NAME = new Name("DFP");
    public static final Name NEGATIVE_LITERAL = new Name("javaUnaryMinusDouble");

    private final JFunction doubleLit;
    private final JFunction lessThan;
    private final JFunction greaterThan;
    private final JFunction greaterOrEquals;
    private final JFunction lessOrEquals;
    private final JFunction eqDouble;

    private final JFunction javaUnaryMinusDouble;
    private final JFunction javaAddDouble;
    private final JFunction javaSubDouble;
    private final JFunction javaMulDouble;
    private final JFunction javaDivDouble;
    private final JFunction javaModDouble;

    private final JFunction javaMinDouble;
    private final JFunction javaMaxDouble;

    private final JFunction addDouble;
    private final JFunction subDouble;
    private final JFunction mulDouble;
    private final JFunction divDouble;
    private final JFunction doubleAbs;
    private final JFunction negDouble;

    private final JFunction isNormal;
    private final JFunction isSubnormal;
    private final JFunction isNaN;
    private final JFunction isZero;
    private final JFunction isNice;
    private final JFunction isInfinite;
    private final JFunction isNegative;
    private final JFunction isPositive;

    private final JFunction sinDouble;
    private final JFunction cosDouble;
    private final JFunction acosDouble;
    private final JFunction asinDouble;
    private final JFunction tanDouble;
    private final JFunction atan2Double;
    private final JFunction sqrtDouble;
    private final JFunction powDouble;
    private final JFunction expDouble;
    private final JFunction atanDouble;

    public DoubleLDT(TermServices services) {
        super(NAME, services);

        doubleLit = addFunction(services, DOUBLELIT_NAME.toString());
        javaUnaryMinusDouble = addFunction(services, NEGATIVE_LITERAL.toString());
        lessThan = addFunction(services, "ltDouble");
        greaterThan = addFunction(services, "gtDouble");
        lessOrEquals = addFunction(services, "leqDouble");
        greaterOrEquals = addFunction(services, "geqDouble");
        eqDouble = addFunction(services, "eqDouble");

        javaAddDouble = addFunction(services, "javaAddDouble");
        javaSubDouble = addFunction(services, "javaSubDouble");
        javaMulDouble = addFunction(services, "javaMulDouble");
        javaDivDouble = addFunction(services, "javaDivDouble");
        javaModDouble = addFunction(services, "javaModDouble");
        javaMaxDouble = addFunction(services, "javaMaxDouble");
        javaMinDouble = addFunction(services, "javaMinDouble");

        addDouble = addFunction(services, "addDouble");
        subDouble = addFunction(services, "subDouble");
        mulDouble = addFunction(services, "mulDouble");
        divDouble = addFunction(services, "divDouble");
        doubleAbs = addFunction(services, "absDouble");
        negDouble = addFunction(services, "negDouble");

        isNormal = addFunction(services, "doubleIsNormal");
        isSubnormal = addFunction(services, "doubleIsSubnormal");
        isNaN = addFunction(services, "doubleIsNaN");
        isZero = addFunction(services, "doubleIsZero");
        isNice = addFunction(services, "doubleIsNice");
        isInfinite = addFunction(services, "doubleIsInfinite");
        isPositive = addFunction(services, "doubleIsPositive");
        isNegative = addFunction(services, "doubleIsNegative");

        sinDouble = addFunction(services, "sinDouble");
        cosDouble = addFunction(services, "cosDouble");
        acosDouble = addFunction(services, "acosDouble");
        asinDouble = addFunction(services, "asinDouble");
        tanDouble = addFunction(services, "tanDouble");
        atan2Double = addFunction(services, "atan2Double");
        sqrtDouble = addFunction(services, "sqrtDouble");
        powDouble = addFunction(services, "powDouble");
        expDouble = addFunction(services, "expDouble");
        atanDouble = addFunction(services, "atanDouble");
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
        if (left != null && left.sort().extendsTrans(targetSort()) && right != null
                && right.sort().extendsTrans(targetSort())) {
            return getFunctionFor(op, services, ec) != null;
        }
        return false;
    }

    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, Term sub,
            TermServices services, ExecutionContext ec) {
        if (sub != null && sub.sort().extendsTrans(targetSort())) {
            return op instanceof Negative;
        }
        return false;
    }


    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert lit instanceof DoubleLiteral : "Literal '" + lit + "' is not a double literal.";
        String s = ((DoubleLiteral) lit).getValue();
        double doubleVal = Double.parseDouble(s);
        return services.getTermBuilder().dfpTerm(doubleVal);
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
    public JFunction getFunctionFor(de.uka.ilkd.key.java.expression.Operator op,
            Services services,
            ExecutionContext ec) {
        if (op instanceof Negative) {
            return getJavaUnaryMinus();
        } else {
            return null;
        }
    }

    @Override
    public boolean hasLiteralFunction(JFunction f) {
        return containsFunction(f) && (f.arity() == 0);
    }

    @Override
    public DoubleLiteral translateTerm(Term t, ExtList children, Services services) {
        JFunction f = (JFunction) t.op();
        IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();

        if (f == doubleLit) {
            // Use IntegerLDT to translate to literals
            String digits = intLDT.toNumberString(t.sub(0));
            long bits = Long.parseUnsignedLong(digits);
            double d1 = Double.longBitsToDouble(bits);

            return new DoubleLiteral(Double.toString(d1));
        }

        throw new RuntimeException("DoubleLDT: Cannot convert term to program: " + t);
    }


    @Override
    public Type getType(Term t) {
        if (t.sort() == targetSort()) {
            return PrimitiveType.JAVA_DOUBLE;
        } else {
            return null;
        }
    }

    public JFunction getDoubleSymbol() {
        return doubleLit;
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
        return eqDouble;
    }

    public JFunction getJavaUnaryMinus() {
        return javaUnaryMinusDouble;
    }

    public JFunction getJavaAdd() {
        return javaAddDouble;
    }

    public JFunction getJavaSub() {
        return javaSubDouble;
    }

    public JFunction getJavaMul() {
        return javaMulDouble;
    }

    public JFunction getJavaDiv() {
        return javaDivDouble;
    }

    public JFunction getJavaMod() {
        return javaModDouble;
    }

    public JFunction getJavaMin() {
        return javaMinDouble;
    }

    public JFunction getJavaMax() {
        return javaMaxDouble;
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
        return addDouble;
    }

    public JFunction getSub() {
        return subDouble;
    }

    public JFunction getMul() {
        return mulDouble;
    }

    public JFunction getDiv() {
        return divDouble;
    }

    public JFunction getAbs() {
        return doubleAbs;
    }

    public JFunction getNeg() {
        return negDouble;
    }

    public JFunction getSinDouble() {
        return sinDouble;
    }

    public JFunction getCosDouble() {
        return cosDouble;
    }

    public JFunction getAcosDouble() {
        return acosDouble;
    }

    public JFunction getAsinDouble() {
        return asinDouble;
    }

    public JFunction getTanDouble() {
        return tanDouble;
    }

    public JFunction getAtan2Double() {
        return atan2Double;
    }

    public JFunction getSqrtDouble() {
        return sqrtDouble;
    }

    public JFunction getPowDouble() {
        return powDouble;
    }

    public JFunction getExpDouble() {
        return expDouble;
    }

    public JFunction getAtanDouble() {
        return atanDouble;
    }
}
