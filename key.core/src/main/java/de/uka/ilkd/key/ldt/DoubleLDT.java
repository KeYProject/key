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
import org.key_project.logic.op.Function;

import de.uka.ilkd.key.logic.op.JavaDLFunction;
import org.key_project.logic.Name;
import org.key_project.util.ExtList;

public final class DoubleLDT extends LDT implements FloatingPointLDT {

    public static final Name NAME = new Name("double");
    public static final Name DOUBLELIT_NAME = new Name("DFP");
    public static final Name NEGATIVE_LITERAL = new Name("javaUnaryMinusDouble");

    private final JavaDLFunction doubleLit;
    private final JavaDLFunction lessThan;
    private final JavaDLFunction greaterThan;
    private final JavaDLFunction greaterOrEquals;
    private final JavaDLFunction lessOrEquals;
    private final JavaDLFunction eqDouble;

    private final JavaDLFunction javaUnaryMinusDouble;
    private final JavaDLFunction javaAddDouble;
    private final JavaDLFunction javaSubDouble;
    private final JavaDLFunction javaMulDouble;
    private final JavaDLFunction javaDivDouble;
    private final JavaDLFunction javaModDouble;

    private final JavaDLFunction javaMinDouble;
    private final JavaDLFunction javaMaxDouble;

    private final JavaDLFunction addDouble;
    private final JavaDLFunction subDouble;
    private final JavaDLFunction mulDouble;
    private final JavaDLFunction divDouble;
    private final JavaDLFunction doubleAbs;
    private final JavaDLFunction negDouble;

    private final JavaDLFunction isNormal;
    private final JavaDLFunction isSubnormal;
    private final JavaDLFunction isNaN;
    private final JavaDLFunction isZero;
    private final JavaDLFunction isNice;
    private final JavaDLFunction isInfinite;
    private final JavaDLFunction isNegative;
    private final JavaDLFunction isPositive;

    private final JavaDLFunction sinDouble;
    private final JavaDLFunction cosDouble;
    private final JavaDLFunction acosDouble;
    private final JavaDLFunction asinDouble;
    private final JavaDLFunction tanDouble;
    private final JavaDLFunction atan2Double;
    private final JavaDLFunction sqrtDouble;
    private final JavaDLFunction powDouble;
    private final JavaDLFunction expDouble;
    private final JavaDLFunction atanDouble;

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
    public JavaDLFunction getFunctionFor(String op, Services services) {
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
    public JavaDLFunction getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, Services services,
                                         ExecutionContext ec) {
        if (op instanceof Negative) {
            return getJavaUnaryMinus();
        } else {
            return null;
        }
    }

    @Override
    public boolean hasLiteralFunction(JavaDLFunction f) {
        return containsFunction(f) && (f.arity() == 0);
    }

    @Override
    public DoubleLiteral translateTerm(Term t, ExtList children, Services services) {
        JavaDLFunction f = (JavaDLFunction) t.op();
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

    public JavaDLFunction getDoubleSymbol() {
        return doubleLit;
    }

    public JavaDLFunction getLessThan() {
        return lessThan;
    }

    public JavaDLFunction getGreaterThan() {
        return greaterThan;
    }

    public JavaDLFunction getLessOrEquals() {
        return lessOrEquals;
    }

    public JavaDLFunction getGreaterOrEquals() {
        return greaterOrEquals;
    }

    public JavaDLFunction getEquals() {
        return eqDouble;
    }

    public JavaDLFunction getJavaUnaryMinus() {
        return javaUnaryMinusDouble;
    }

    public JavaDLFunction getJavaAdd() {
        return javaAddDouble;
    }

    public JavaDLFunction getJavaSub() {
        return javaSubDouble;
    }

    public JavaDLFunction getJavaMul() {
        return javaMulDouble;
    }

    public JavaDLFunction getJavaDiv() {
        return javaDivDouble;
    }

    public JavaDLFunction getJavaMod() {
        return javaModDouble;
    }

    public JavaDLFunction getJavaMin() {
        return javaMinDouble;
    }

    public JavaDLFunction getJavaMax() {
        return javaMaxDouble;
    }

    public JavaDLFunction getIsNormal() {
        return isNormal;
    }

    public JavaDLFunction getIsSubnormal() {
        return isSubnormal;
    }

    public JavaDLFunction getIsNaN() {
        return isNaN;
    }

    public JavaDLFunction getIsZero() {
        return isZero;
    }

    @Override
    public JavaDLFunction getIsNice() {
        return isNice;
    }

    public JavaDLFunction getIsInfinite() {
        return isInfinite;
    }

    public JavaDLFunction getIsPositive() {
        return isPositive;
    }

    public JavaDLFunction getIsNegative() {
        return isNegative;
    }

    public JavaDLFunction getAdd() {
        return addDouble;
    }

    public JavaDLFunction getSub() {
        return subDouble;
    }

    public JavaDLFunction getMul() {
        return mulDouble;
    }

    public JavaDLFunction getDiv() {
        return divDouble;
    }

    public JavaDLFunction getAbs() {
        return doubleAbs;
    }

    public JavaDLFunction getNeg() {
        return negDouble;
    }

    public JavaDLFunction getSinDouble() {
        return sinDouble;
    }

    public JavaDLFunction getCosDouble() {
        return cosDouble;
    }

    public JavaDLFunction getAcosDouble() {
        return acosDouble;
    }

    public JavaDLFunction getAsinDouble() {
        return asinDouble;
    }

    public JavaDLFunction getTanDouble() {
        return tanDouble;
    }

    public JavaDLFunction getAtan2Double() {
        return atan2Double;
    }

    public JavaDLFunction getSqrtDouble() {
        return sqrtDouble;
    }

    public JavaDLFunction getPowDouble() {
        return powDouble;
    }

    public JavaDLFunction getExpDouble() {
        return expDouble;
    }

    public JavaDLFunction getAtanDouble() {
        return atanDouble;
    }
}
