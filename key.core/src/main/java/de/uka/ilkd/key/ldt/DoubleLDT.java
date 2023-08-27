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
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;

import org.key_project.util.ExtList;

public final class DoubleLDT extends LDT implements FloatingPointLDT {

    public static final Name NAME = new Name("double");
    public static final Name DOUBLELIT_NAME = new Name("DFP");
    public static final Name NEGATIVE_LITERAL = new Name("javaUnaryMinusDouble");

    private final Function doubleLit;
    private final Function lessThan;
    private final Function greaterThan;
    private final Function greaterOrEquals;
    private final Function lessOrEquals;
    private final Function eqDouble;

    private final Function javaUnaryMinusDouble;
    private final Function javaAddDouble;
    private final Function javaSubDouble;
    private final Function javaMulDouble;
    private final Function javaDivDouble;
    private final Function javaModDouble;

    private final Function javaMinDouble;
    private final Function javaMaxDouble;

    private final Function addDouble;
    private final Function subDouble;
    private final Function mulDouble;
    private final Function divDouble;
    private final Function doubleAbs;
    private final Function negDouble;

    private final Function isNormal;
    private final Function isSubnormal;
    private final Function isNaN;
    private final Function isZero;
    private final Function isNice;
    private final Function isInfinite;
    private final Function isNegative;
    private final Function isPositive;

    private final Function sinDouble;
    private final Function cosDouble;
    private final Function acosDouble;
    private final Function asinDouble;
    private final Function tanDouble;
    private final Function atan2Double;
    private final Function sqrtDouble;
    private final Function powDouble;
    private final Function expDouble;
    private final Function atanDouble;

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
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, Services services,
            ExecutionContext ec) {
        if (op instanceof Negative) {
            return getJavaUnaryMinus();
        } else {
            return null;
        }
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return containsFunction(f) && (f.arity() == 0);
    }

    @Override
    public DoubleLiteral translateTerm(Term t, ExtList children, Services services) {
        Function f = (Function) t.op();
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

    public Function getDoubleSymbol() {
        return doubleLit;
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
        return eqDouble;
    }

    public Function getJavaUnaryMinus() {
        return javaUnaryMinusDouble;
    }

    public Function getJavaAdd() {
        return javaAddDouble;
    }

    public Function getJavaSub() {
        return javaSubDouble;
    }

    public Function getJavaMul() {
        return javaMulDouble;
    }

    public Function getJavaDiv() {
        return javaDivDouble;
    }

    public Function getJavaMod() {
        return javaModDouble;
    }

    public Function getJavaMin() {
        return javaMinDouble;
    }

    public Function getJavaMax() {
        return javaMaxDouble;
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
        return addDouble;
    }

    public Function getSub() {
        return subDouble;
    }

    public Function getMul() {
        return mulDouble;
    }

    public Function getDiv() {
        return divDouble;
    }

    public Function getAbs() {
        return doubleAbs;
    }

    public Function getNeg() {
        return negDouble;
    }

    public Function getSinDouble() {
        return sinDouble;
    }

    public Function getCosDouble() {
        return cosDouble;
    }

    public Function getAcosDouble() {
        return acosDouble;
    }

    public Function getAsinDouble() {
        return asinDouble;
    }

    public Function getTanDouble() {
        return tanDouble;
    }

    public Function getAtan2Double() {
        return atan2Double;
    }

    public Function getSqrtDouble() {
        return sqrtDouble;
    }

    public Function getPowDouble() {
        return powDouble;
    }

    public Function getExpDouble() {
        return expDouble;
    }

    public Function getAtanDouble() {
        return atanDouble;
    }
}
